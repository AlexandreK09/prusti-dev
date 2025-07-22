use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutputRef, FieldFunctions, FieldTy}, generic, lifted::{ty::{EncodeGenericsAsParamTy, LiftedTy, LiftedTyEnc}, ty_constructor::TyConstructorEnc}, pair_ref_type::PairRefTypeOutputRef, predicate::PredicateBuilder, rust_ty_predicates::RustTyPredicatesEncOutputRef, snapshot::SnapshotEncOutput, GenericEnc, PredicateEnc
};
use crate::encoders::most_generic_ty::extract_type_params;
use prusti_rustc_interface::middle::ty::{ParamTy, TyKind};
use prusti_rustc_interface::middle::mir::Mutability;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CastType, Expr, FunctionIdn, HasType, ManySnap, ManyTyVal, PredicateIdn, VirCtxt};

use prusti_rustc_interface::middle::ty::Ty;

pub fn domain<'vir>(
    prefix: &str,
    fields: &[FieldTy<'vir>],
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    generics: &[ParamTy],
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<
    (
        FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal), vir::CSnap>,
        &'vir [FieldFunctions<'vir>],
        Vec<vir::LocalSnap<'vir>>,
    ),
    EncodeFullError<'vir, DomainEnc>,
> {
    let generic_enc = deps.require_ref::<GenericEnc>(())?;

    // constructor
    let cons_ident = builder.function::<(ManySnap, ManyTyVal), vir::CSnap>(
        &format!("{prefix}cons"),
        (
            builder
                .vcx
                .alloc_slice(&fields.iter().map(|fty| fty.ty).collect::<Vec<_>>()),
            builder
                .vcx
                .alloc_slice(&generics.iter().map(|_| generic_enc.type_snapshot).collect::<Vec<_>>())
        ),
        builder.self_type(),
    );

    // field accessors
    let field_reads = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(&format!("{prefix}read_{idx}"), builder.self_type(), ty.ty)
        })
        .collect::<Vec<_>>();
    let field_writes = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(
                &format!("{prefix}write_{idx}"),
                (builder.self_type(), ty.ty),
                builder.self_type(),
            )
        })
        .collect::<Vec<_>>();

    // variables for quantifiers
    let generic_vars = generics
        .iter()
        .map(|g| {
            builder
            .vcx
            .mk_local(builder.vcx.alloc_str(g.name.as_str()), generic_enc.type_snapshot)
        })
        .collect::<Vec<_>>();
    let field_vars = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder
                .vcx
                .mk_local(vir_format!(builder.vcx, "f{idx}"), ty.ty)
        })
        .collect::<Vec<_>>();
    let qvars = field_vars
        .iter()
        .cloned()
        .map(|var| var.as_dyn())
        .chain(generic_vars.iter().cloned().map(|var| var.as_dyn()))
        .collect::<Vec<_>>();

    // TODO: typeof and read_type axioms
    /*
    // for struct U<T> { x: T, y: i32 }
    // this one forwards the generic
    axiom ax_s_U_read_0_type {
        forall self: s_U :: {s_U_read_0(self)} (typ(s_U_read_0(self))) == (s_U_typaram_T(typeof_s_U(self)))
    }
    // this one seems less useful: this could be an axiom over s_Int_i32_typeof generally?
    axiom ax_s_U_read_1_type {
        forall self: s_U :: {s_U_read_1(self)} (s_Int_i32_typeof(s_U_read_1(self))) == (s_Int_i32_type())
    }
    axiom ax_typeof_s_U {
        forall self: s_U :: {s_U_typaram_T(typeof_s_U(self))} (typeof_s_U(self)) == (s_U_type(s_U_typaram_T(typeof_s_U(self))))
    }
    */

    let ty_cons = deps.require_ref::<TyConstructorEnc>(task_key)?;
    if prefix.is_empty() {
        // TODO: this ensures that we only produce one axiom for enums, but the
        //   check based on prefix is not very clean
        builder.axiom("typeof", vir::expr! {
            forall s: [builder.self_type()] ::
                {[output_ref.typeof_function]((s) as Snap)}
                ([output_ref.typeof_function]((s) as Snap)) == ([ty_cons.ty_constructor](..[generics.iter()
                    .enumerate()
                    .map(|(param_idx, _)| {
                        vir::expr! { [output_ref.ty_param_accessors[param_idx]]([output_ref.typeof_function]((s) as Snap)) }
                        // output_ref.ty_param_accessors[param_idx].apply(builder.vcx, [output_ref.typeof_function.apply(builder.vcx, [s])])
                    })
                    .collect::<Vec<_>>()
                    .as_slice()]))
        });
    }

    let field_vars_expr = builder.vcx.alloc_slice(&field_vars.iter().map(|local| builder.vcx.mk_local_ex_local(local)).collect::<Vec<_>>());
    let generic_exprs = builder.vcx.alloc_slice(&generic_vars.iter().map(|local| builder.vcx.mk_local_ex_local(local)).collect::<Vec<_>>());
    let cons = cons_ident.gen()(field_vars_expr, generic_exprs).upcast_ty();
    let qvars = builder.vcx.alloc_slice(&qvars.iter().map(|local| builder.vcx.mk_local_decl_local(local)).collect::<Vec<_>>());
    builder.axiom(
        &format!("{prefix}cons_type"),
        builder.vcx.mk_forall_expr(
            qvars,
            builder.vcx.alloc_slice(&[builder.vcx.mk_trigger(builder.vcx.alloc_slice(&[cons]))]),
            builder.vcx.mk_eq_expr(output_ref.typeof_function.gen()(cons), ty_cons.ty_constructor.gen()(generic_exprs))
        )
        /*vir::expr! {
            forall ..[qvars] ::
                {cons}
                ([output_ref.typeof_function](cons)) == ([ty_cons.ty_constructor](..[generic_exprs]))
        }*/    
    );

    let mut cons_read_preconditions = Vec::new();

    let generic_types = generic_vars.iter().map(|&local| builder.vcx.mk_local_ex_local(local)).collect::<Vec<_>>();
    for idx in 0..fields.len(){
        let field = &fields[idx];
        let local = field_vars[idx];

        let most_generic = extract_type_params(builder.vcx.tcx.unwrap(), field.rust_ty).0;
        let field_type_domain = deps.require_ref::<DomainEnc>(most_generic)?;
        let actual_type = vir::expr! {
            [field_type_domain.typeof_function](local)
        };
        
        let lifted = deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(field.rust_ty)?;
        let expected_type = type_snapshot_with_generic_expr(lifted, &generic_types, builder.vcx);
        let eq = builder.vcx.mk_eq_expr(actual_type, expected_type);
        cons_read_preconditions.push(eq);
    }

    
    let cons_read_precondition = builder.vcx.mk_conj(&cons_read_preconditions);
    // field accessor axioms
    for idx in 0..fields.len() {
        let lhs = field_reads[idx].gen()(cons.downcast_ty());
        builder.axiom(
            &format!("{prefix}cons_read_{idx}"),
            builder.vcx.mk_forall_expr(
                qvars, 
                builder.vcx.alloc_slice(&[builder.vcx.mk_trigger(builder.vcx.alloc_slice(&[cons]))]),
                builder.vcx.mk_bin_op_expr(vir::BinOpKind::Implies, 
                    cons_read_precondition, 
                    builder.vcx.mk_eq_expr(lhs, builder.vcx.mk_local_ex_local(field_vars[idx]))).downcast_ty()
            )
            /*vir::expr! {
                forall ..[qvars] ::
                    {cons}
                    (cons_read_precondition) ==> ((lhs) == ([field_vars[idx]]))
            },*/
        );

        // if let TyKind::Param(p) = fields[idx].rust_ty.kind() {
        //     // TODO: this only handles top-level generics
        //     let param_idx = p.index as usize;
        //     builder.axiom(&format!("{prefix}type_read_{idx}"), vir::expr! {
        //         forall s: [builder.self_type()] ::
        //             {[field_reads[idx]](s)}
        //             ([generic_enc.param_type_function]([field_reads[idx]](s))) == ([output_ref.ty_param_accessors[param_idx]]([output_ref.typeof_function](s)))
        //     });
        // }

        //type axioms for fields
        let s_ex = builder.vcx.mk_local_ex("s", builder.self_type());

        let typeof_snap_expr = output_ref.typeof_function.gen()(s_ex.upcast_ty());

        let generic_types = output_ref.ty_param_accessors.iter().map(|acc| acc.gen()(typeof_snap_expr)).collect::<Vec<_>>();

        let lifted = deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(fields[idx].rust_ty)?;

        let rhs = type_snapshot_with_generic_expr(lifted, &generic_types, builder.vcx);
        let lhs = {
            let most_generic = extract_type_params(builder.vcx.tcx.unwrap(), fields[idx].rust_ty).0;
            let output_ref = deps.require_ref::<DomainEnc>(most_generic)?;
            vir::expr!{
                [output_ref.typeof_function]([field_reads[idx]](s_ex))
            }
        };
        builder.axiom(&format!("{prefix}type_read_{idx}"), vir::expr! {
            forall s: [builder.self_type()] ::
                {[field_reads[idx]](s)}
                ([lhs]) == ([rhs])
        });
    }
    for write_idx in 0..fields.len() {
        for read_idx in 0..fields.len() {
            // TODO: is the trigger here too specific? we could trigger on the read already?
            builder.axiom(&format!("{prefix}write_{write_idx}_read_{read_idx}"), if read_idx == write_idx {
                vir::expr! {
                    forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                        {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                        ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == (value)
                }
            } else {
                vir::expr! {
                    forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                        {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                        ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == ([field_reads[read_idx]](s))
                }
            });
        }
    }

    let field_access = field_reads
        .into_iter()
        .zip(field_writes)
        .map(|(read, write)| FieldFunctions {
            read: read,
            write: write,
        })
        .collect::<Vec<_>>();

    Ok((
        cons_ident,
        builder.vcx.alloc_slice(&field_access),
        field_vars,
    ))
}

fn type_snapshot_with_generic_expr<'vir>(
    lifted: LiftedTy<'vir, ParamTy>,
    generic_types: &[Expr<'vir, vir::TyVal>],
    vcx: &'vir VirCtxt<'vir>
) -> Expr<'vir, vir::TyVal>{
    lifted.map(vcx, &mut |g: ParamTy| generic_types[g.index as usize]).expr(vcx)
}

pub(crate) fn predicate<'vir>(
    prefix: &str,
    fields: &[RustTyPredicatesEncOutputRef<'vir>],
    fields_snap: &'vir [FieldFunctions<'vir>],
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: &SnapshotEncOutput<'vir>,
    pair: &PairRefTypeOutputRef<'vir>,
    variant_field_snaps_to_snap: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal), vir::CSnap>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>>,
        PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
        vir::ExprCSnap<'vir>,
        vir::Expr<'vir, vir::Set<vir::PairRefType>>
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    /*
        let snap_data = snap.specifics.expect_structlike();
        let fields = variant
        .fields
        .iter()
        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
        .collect::<Vec<_>>();
    */

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let generic_decls_tys = builder.vcx.alloc_slice(
        generic_decls
            .iter()
            .copied()
            .map(vir::LocalDeclData::ty)
            .collect::<Vec<_>>()
            .as_slice(),
    );
    // Ref-to-Ref function for every field
    let field_accessors: Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>> = fields
        .iter()
        .enumerate()
        .map(|(idx, _field)| {
            builder.function::<(vir::Ref, vir::ManyTyVal), vir::Ref>(
                &format!("{prefix}field_{idx}"),
                (ref_self_decl.ty(), generic_decls_tys),
                vir::TYPE_REF,
                (ref_self_decl, generic_decls),
                &[], // TODO: should have a read permission here!
                &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                None,
            )
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder.predicate::<(vir::Ref, vir::ManyTyVal)>(
        &pred_name,
        (ref_self_decl.ty(), generic_decls_tys),
        (ref_self_decl, generic_decls),
        Some(
            builder.vcx.mk_conj(
                &fields
                    .iter()
                    .zip(&field_accessors)
                    .map(|(field, accessor)| {
                        field.ref_to_pred(builder.vcx, accessor(ref_self_ex, &generic_exprs), None)
                    })
                    .collect::<Vec<_>>(),
            ),
        ),
    );

    // Ref-to-snap
    let snap_args = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| {
            field.ref_to_snap(builder.vcx, accessor(ref_self_ex, &generic_exprs))
        })
        //.chain(generic_exprs.iter().cloned())
        .collect::<Vec<_>>();
    let snap_args = builder.vcx.alloc_slice(&snap_args);
    let snapped = variant_field_snaps_to_snap.gen()(snap_args, generic_exprs);
    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, ..[generic_exprs])) in (snapped)
    };

    let var_snap = builder.vcx.mk_local("snap", snap_type);
    let var_snap_ex = builder.vcx.mk_local_ex_local(var_snap);

    let get_unsafe_cells_expr  = fields
        .iter()
        .zip(&field_accessors)
        .zip(fields_snap.iter())
        .map(|((field, accessor), field_snap)| {
            field.ref_to_get_unsafe_cells(
                builder.vcx,
                accessor.gen()(
                    ref_self_ex,
                    generic_exprs
                ),
                field_snap.read.gen()(var_snap_ex),
            )
        })
        .reduce(|lhs, rhs|
            builder.vcx.mk_set_union(lhs, rhs)
        )
        .unwrap_or(builder.vcx.mk_set_literal_expr(&[], vir::TYPE_PAIR));

    let snapped = variant_field_snaps_to_snap.gen()(snap_args, generic_exprs);
    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, ..[generic_exprs])) in (snapped)
    };

    /*
    let pred_owned_expr = vir::expr! {
        (([discr_ty_out.ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]))])
            == ([snap_variant.discr])) => ([pred_owned](ref_self))
    };
    */

    /*
    let variant = adt.non_enum_variant();
    let fields = variant
        .fields
        .iter()
        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
        .collect::<Vec<_>>();

    // Ref-to-Ref function for every field
    let field_accessors = fields.iter()
        .enumerate()
        .map(|(idx, _field)| builder.function(
            &format!("field_{idx}"),
            &[ref_self_decl],
            &vir::TypeData::Ref,
            &[],
            &[
                vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
            ],
            None,
        ))
        .collect::<Vec<_>>();

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl],
        Some(builder.vcx.mk_conj(&fields.iter()
            .zip(&field_accessors)
            .map(|(field, accessor)| field.ref_to_pred(builder.vcx, accessor.apply(builder.vcx, &[ref_self_ex]), None))
            .collect::<Vec<_>>())),
    );

    // Ref-to-snap
    let snap_args = fields.iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| field.ref_to_snap(builder.vcx, accessor.apply(builder.vcx, &[ref_self_ex])))
        .collect::<Vec<_>>();
    builder.function_snap = Some(builder.mk_function(
        "snap",
        &[ref_self_decl],
        snap_type,
        &[vir::expr! { acc([self_pred](ref_self)) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self)) in ([snap_data.field_snaps_to_snap](..[snap_args]))
        }),
    ).1);

    /*
    // lifetime projection predicates
    let _lft_predicates = params.iter()
        .enumerate()
        .flat_map(|(reg_idx, arg)| Some((reg_idx, arg.as_region()?)))
        .map(|(reg_idx, reg)| builder.predicate(
                &format!("lft_{reg_idx}"),
                &[snap_self_decl],
                Some(builder.vcx.mk_conj(&fields.iter()
                    .zip(&variant.fields)
                    .enumerate()
                    .filter_map(|(field_idx, (field, rust_field))| match rust_field.ty(builder.vcx.tcx(), params).kind() {
                        ty::TyKind::Ref(field_reg, inner_ty, ty::Mutability::Mut) => {
                            if *field_reg != reg {
                                return None;
                            }
                            let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                            Some(inner_ty_enc.ref_to_pred(
                                builder.vcx,
                                field.generic_predicate.expect_ref().snap_data.deref_access.apply(builder.vcx, [
                                    snap_data.field_access[field_idx].read.apply(builder.vcx, [snap_self_ex]),
                                ]),
                                None,
                            ))
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>()))
            ))
        .collect::<Vec<_>>();
    */

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors.iter()
            .map(|f| f)
            .collect::<Vec<_>>()),
    }))
    */
    Ok((field_accessors, pred_owned, variant_snap_expr, get_unsafe_cells_expr))
}
