use std::{cell::UnsafeCell, iter::once};

use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{indirect, kinds::param, lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc}, most_generic_ty};

use super::{lifted::{self, casters::{CastTypePure, CastersEnc, CastersEncOutputRef}}, most_generic_ty::extract_type_params, rust_ty_predicates::RustTyPredicatesEnc, rust_ty_snapshots::RustTySnapshotsEnc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndirectKey {
    Early(ty::EarlyParamRegion),
    Late(ty::BoundRegionKind),
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
            RegionKind::RePlaceholder(..)
            | RegionKind::ReError(..)
            | RegionKind::ReErased
            | RegionKind::ReVar(..)
            | RegionKind::ReLateParam(..) => unreachable!(),
            RegionKind::ReStatic => None,
        }
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::Expr<'vir>;
type ExprOutput<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub covariant: Vec<ExprOutput<'vir>>,
    pub contravariant: Vec<ExprOutput<'vir>>,
    pub unsafe_cells: Vec<ExprOutput<'vir>>,
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
            let mut covariant = Vec::new();
            let mut contravariant = Vec::new();
            let mut unsafe_cells = Vec::new();
            match ty.kind() {
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) => {
                    let deref_access = self_ty_enc
                        .generic_snapshot
                        .specifics
                        .expect_mutref()
                        .deref_access;
                    if IndirectKey::from_region(*ref_region)
                        .is_some_and(|indirect| &indirect == proj_region)
                    {
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty)?;
                        covariant.push({
                            let inner_ty_enc = inner_ty_enc.clone();
                            vcx.mk_lazy_expr(
                                "ref_indirect",
                                &vir::TypeData::Predicate,
                                Box::new(move |vcx, self_expr| {
                                    inner_ty_enc
                                        .ref_to_pred(vcx, deref_access.apply(vcx, [self_expr]), None)
                                        .kind
                                }),
                            )
                        });
                        //Todo: also add "old" where needed 
                        unsafe_cells.push(vcx.mk_lazy_expr(
                            "ref_indirect",
                            &vir::TypeData::Predicate,
                            Box::new(move |vcx, self_expr| {
                                let self_ref = deref_access.apply(vcx, [self_expr]);
                                let snap = inner_ty_enc.ref_to_snap(vcx, self_ref);
                                inner_ty_enc
                                    .ref_to_get_unsafe_cells(vcx, self_ref, snap)
                                    .kind
                            }),
                        ));
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
                                &vir::TypeData::Predicate,
                                Box::new(move |vcx, self_expr| {
                                    inner_expr
                                        .reify(vcx, deref_access.apply(vcx, [self_expr]))
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
                            &vir::TypeData::Predicate,
                            Box::new(move |vcx, self_expr| {
                                let self_ref = deref_access.apply(vcx, [self_expr]);
                                let s_param = self_ty_enc.generic_snapshot
                                    .specifics
                                    .expect_immref()
                                    .value_access
                                    .apply(vcx, [self_expr]);
                                let snap = match &caster {
                                    None => s_param,
                                    Some((make_concrete, typarams)) => make_concrete.apply(
                                        vcx, 
                                        vcx.alloc_slice(
                                            &once(s_param)
                                            .chain(typarams.iter().cloned())
                                            .collect::<Vec<_>>()
                                        )
                                    )
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
                        let (most_generic, typarams) = extract_type_params(vcx.tcx(), field_ty);
                        let caster = deps.require_ref::<CastersEnc<CastTypePure>>(most_generic)?;

                        if let CastersEncOutputRef::Casters { make_concrete, .. } = caster {
                            let cast_args = typarams.into_iter().map(|typaram| {
                                let lifted = deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(typaram)?;
                                Ok(lifted.expr(vcx))
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                            let cast_args = vcx.alloc_slice(&cast_args);

                            let project = |inner_expr: ExprOutput<'vir>, cast_args: &'vir [&'vir vir::ExprGenData<'vir, !, !>]| {
                                vcx.mk_lazy_expr(
                                    "ref_inner_indirect",
                                    &vir::TypeData::Predicate,
                                    Box::new(move |vcx, self_expr| {
                                        let s_param = accessor.read.apply(vcx, [self_expr]);
                                        let reify_arg = make_concrete.apply(
                                            vcx, 
                                            vcx.alloc_slice(
                                                &[s_param].iter()
                                                    .chain(cast_args.iter())
                                                    .cloned()
                                                    .collect::<Vec<_>>()
                                            )
                                        );
                                        inner_expr
                                            .reify(vcx, reify_arg)
                                            .kind
                                    }),
                                )
                            };

                            let field_indirect =
                                deps.require_ref::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                            covariant.extend(field_indirect.covariant.into_iter().map(|e| project(e, cast_args)));
                            contravariant.extend(field_indirect.contravariant.into_iter().map(|e| project(e, cast_args)));
                            unsafe_cells.extend(field_indirect.unsafe_cells.into_iter().map(|e| project(e, cast_args)));
                        }else {
                            let project = |inner_expr: ExprOutput<'vir>| {
                                vcx.mk_lazy_expr(
                                    "ref_inner_indirect",
                                    &vir::TypeData::Predicate,
                                    Box::new(move |vcx, self_expr| {
                                        inner_expr
                                            .reify(vcx, accessor.read.apply(vcx, [self_expr]))
                                            .kind
                                    }),
                                )
                            };

                            let field_indirect =
                                deps.require_ref::<IndirectPredicatesEnc>((field_ty, *proj_region))?;
                            covariant.extend(field_indirect.covariant.into_iter().map(project));
                            contravariant.extend(field_indirect.contravariant.into_iter().map(project));
                            unsafe_cells.extend(field_indirect.unsafe_cells.into_iter().map(project));
                        }
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
                    unsafe_cells
                },
            )?;
            Ok(((), ()))
        })
    }
}
