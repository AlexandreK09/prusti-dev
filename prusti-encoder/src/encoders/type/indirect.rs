use std::{cell::UnsafeCell, iter::once};
use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, PSnap, PairRefType, Reify};

use crate::encoders::{indirect, kinds::param, lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc}, most_generic_ty};

use super::{lifted::{self, casters::{CastTypePure, CastersEnc, CastersEncOutputRef}}, most_generic_ty::extract_type_params, rust_ty_predicates::RustTyPredicatesEnc, rust_ty_snapshots::RustTySnapshotsEnc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndirectKey {
    Early(ty::EarlyParamRegion),
    Late(ty::BoundRegionKind),
    Var(ty::RegionVid),
    Param(ty::ParamTy),
}

impl IndirectKey {
    pub fn from_generic_arg(ga: ty::GenericArg) -> Option<Self> {
        match ga.unpack() {
            ty::GenericArgKind::Lifetime(region) => Self::from_region(region),
            ty::GenericArgKind::Type(ty) => match *ty.kind() {
                ty::TyKind::Param(p) => Some(IndirectKey::Param(p)),
                _ => None,
            },
            ty::GenericArgKind::Const(_) => None,
        }
    }

    pub fn from_region(region: ty::Region) -> Option<Self> {
        use ty::RegionKind;
        match region.kind() {
            RegionKind::ReEarlyParam(e) => Some(IndirectKey::Early(e)),
            RegionKind::ReBound(_, g) => Some(IndirectKey::Late(g.kind)),
            RegionKind::ReLateParam(r) => Some(IndirectKey::Late(r.bound_region)),
            RegionKind::ReVar(r) => Some(IndirectKey::Var(r)),
            RegionKind::RePlaceholder(..) | RegionKind::ReError(..) | RegionKind::ReErased => {
                unreachable!("{region:?}")
            }
            RegionKind::ReStatic => None,
        }
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub covariant: Vec<ExprOutput<'vir>>,
    pub contravariant: Vec<ExprOutput<'vir>>,
    //pub unsafe_cells: Vec<vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>, vir::Set<vir::PairRefType>>>,
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = (ty::Ty<'vir>, IndirectKey);

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputRef<'vir> = IndirectPredicatesEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let (ty, proj_region) = task_key;
            let self_ty_enc = deps.require_local::<RustTySnapshotsEnc>(*ty)?;
            let mut covariant = Vec::<ExprOutput<'vir>>::new();
            let mut contravariant = Vec::<ExprOutput<'vir>>::new();
            let mut unsafe_cells: Vec<vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>, vir::Set<vir::PairRefType>>> = Vec::new();
            match ty.kind() {
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) => {
                    let ref_domain = self_ty_enc.generic_snapshot.specifics.expect_mutref();
                    if IndirectKey::from_region(*ref_region)
                        .is_some_and(|indirect| &indirect == proj_region)
                    {
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty)?;
                        covariant.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vir::TYPE_BOOL,
                            Box::new(move |vcx, self_expr| {
                                inner_ty_enc
                                    .ref_to_pred(
                                        vcx,
                                        (ref_domain.deref_access)(self_expr.downcast_ty()),
                                        None,
                                    )
                                    .kind
                            }),
                        ));
                        //Todo: also add "old" where needed 
                        /*unsafe_cells.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vcx.mk_ty_set(vir::TYPE_PAIR),
                            Box::new(move |vcx, self_expr| {
                                let self_ref = ref_domain.deref_access.gen()(self_expr.downcast_ty());
                                let snap = inner_ty_enc.ref_to_snap(vcx, self_ref);
                                inner_ty_enc
                                    .ref_to_get_unsafe_cells(vcx, self_ref, snap)
                                    .kind
                            }),
                        ));*/
                    }

                    // TODO: is this correct??? do we always project into the inner type, regardless of region?
                    let inner_indirect =
                        deps.require_ref::<IndirectPredicatesEnc>((*inner_ty, *proj_region))?;
                    let inner = inner_indirect
                        .covariant
                        .into_iter()
                        .chain(inner_indirect.contravariant)
                        .map(|inner_expr| {
                            vcx.mk_lazy_expr(
                                "ref_inner_indirect",
                                vir::TYPE_BOOL,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    inner_expr
                                        .reify(
                                            vcx,
                                            (ref_domain.value_access)(self_expr.downcast_ty())
                                                .upcast_ty(),
                                        )
                                        .kind
                                }),
                            )
                        })
                        .collect::<Vec<_>>();
                    covariant.extend(inner.clone());
                    contravariant.extend(inner);

                }
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Not) => {
                    let deref_access = self_ty_enc
                        .generic_snapshot
                        .specifics
                        .expect_immref()
                        .deref_access;
                    if IndirectKey::from_region(*ref_region)
                        .is_some_and(|indirect| &indirect == proj_region)
                    {
                        let (most_generic, typarams) = extract_type_params(vcx.tcx(), *inner_ty);
                        let caster = deps.require_ref::<CastersEnc<CastTypePure>>(most_generic)?;
                        let caster = match caster{
                            CastersEncOutputRef::AlreadyGeneric => None,
                            CastersEncOutputRef::Casters { make_concrete, .. } => {
                                let typarams_expr = typarams.into_iter()
                                    .map(|ty| {
                                        let lifted = deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(ty)?;
                                        Ok(lifted.expr(vcx))
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;
                                Some((make_concrete, typarams_expr))
                            }
                        };
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty)?;
                        unsafe_cells.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            vcx.mk_ty_set(vir::TYPE_PAIR),
                            Box::new(move |vcx, self_expr| {
                                let self_ref = deref_access.gen()(self_expr.downcast_ty());
                                let s_param = self_ty_enc.generic_snapshot
                                    .specifics
                                    .expect_immref()
                                    .value_access
                                    .gen()(self_expr.downcast_ty());
                                let snap = match &caster {
                                    None => s_param.upcast_ty(),
                                    Some((make_concrete, typarams)) => make_concrete.gen()(s_param, typarams).upcast_ty()
                                };
                                inner_ty_enc
                                    .ref_to_get_unsafe_cells(vcx, self_ref, snap)
                                    .kind
                            }),
                        ));
                    }
                }
                ty::TyKind::Tuple(params) => {
                    let field_accessors = self_ty_enc
                        .generic_snapshot
                        .specifics
                        .expect_structlike()
                        .field_access;
                    for (field_ty, accessor) in params.into_iter().zip(field_accessors) {
                        let project = |inner_expr: ExprOutput<'vir>| {
                            vcx.mk_lazy_expr(
                                "ref_inner_indirect",
                                vir::TYPE_BOOL,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    inner_expr
                                        .reify(vcx, (accessor.read)(self_expr.downcast_ty()))
                                        .kind
                                }),
                            )
                        };

                        // TODO: tuple generics need to be passed to field accessors
                        // TODO: tuple fields need to be (snapshot) cast
                        let field_indirect =
                            deps.require_ref::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                        covariant.extend(field_indirect.covariant.into_iter().map(project));
                        contravariant.extend(field_indirect.contravariant.into_iter().map(project));
                    }
                }
                // TODO: recurse into other types
                _ => (),
            }
            deps.emit_output_ref(
                *task_key,
                IndirectPredicatesEncOutputRef {
                    covariant,
                    contravariant,
                    //unsafe_cells
                },
            )?;
            Ok(((), ()))
        })
    }
}
