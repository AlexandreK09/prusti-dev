use crate::encoders::{
    domain::{DomainBuilder, DomainDataImmRef, DomainEnc, DomainEncSpecifics}, 
    lifted::ty_constructor::TyConstructorEnc, 
    pair_ref_type::PairRefTypeOutputRef, 
    predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataImmRef}, 
    rust_ty_snapshots::RustTySnapshotsEnc, 
    snapshot::SnapshotEncOutput, 
    GenericEnc, 
    PredicateEnc
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdent, ToKnownArity, UnknownArity};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    typeof_ident: FunctionIdent<'vir, UnknownArity<'vir>>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Ref(_, inner_ty, ty::Mutability::Not) = ty_kind else {
        unreachable!();
    };

    let inner_ty_out = deps.require_ref::<RustTySnapshotsEnc>(*inner_ty)?;
    let inner_type = inner_ty_out.generic_snapshot.snapshot;

    let generic_output_ref = deps.require_ref::<GenericEnc>(())?;

    let prim_type = &vir::TypeData::Ref;

    let deref_ident = builder.function("deref", &[builder.self_type()], prim_type);
    let value_ident = builder.function("value", &[builder.self_type()], inner_type);
    let cons_ident = builder.function("cons", &[prim_type, inner_type], builder.self_type());

    let ty_constructor  = deps.require_ref::<TyConstructorEnc>(task_key)?;

    builder.axiom("deref", vir::expr! {
        forall r: [prim_type], value: [inner_type] :: {[cons_ident](r, value)} ([deref_ident]([cons_ident](r, value))) == (r)
    });
    builder.axiom("value", vir::expr! {
        forall r: [prim_type], value: [inner_type] :: {[cons_ident](r, value)} ([value_ident]([cons_ident](r, value))) == (value)
    });
    builder.axiom("type", vir::expr! {
        forall s: [builder.self_type()] :: ([typeof_ident](s)) == ([ty_constructor.ty_constructor]([generic_output_ref.param_type_function]([value_ident](s))))
    });
    // builder.axiom("cons", vir::expr! {
    //     forall s: [builder.self_type()] :: {[deref_ident](s)} ([cons_ident]([deref_ident](s))) == (s)
    // });

    // TODO: was this an axiom we had???
    /*
    match ty_kind {
        ty::TyKind::Int(_) => {
            let min = builder.vcx.get_min_int(&ty_kind);
            let max = builder.vcx.get_max_int(&ty_kind);
            builder.axiom("bounds", vir::expr! {
                forall s: [builder.self_type()] :: {[deref_ident](s)} (([min]) <= ([deref_ident](s))) && (([deref_ident](s)) <= ([max]))
            });
        }
        _ => (),
    }
    */

    Ok(DomainEncSpecifics::ImmRef(DomainDataImmRef {
        prim_to_snap: cons_ident.to_known(),
        deref_access: deref_ident.to_known(),
        value_access: value_ident.to_known(),
    }))
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    pair: &PairRefTypeOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        PredicateEncData<'vir>,
        Option<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Ref(_, _inner_ty, ty::Mutability::Not) = ty_kind else {
        unreachable!();
    };

    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let snap_data = snap.specifics.expect_immref();
    let generic = deps.require_ref::<GenericEnc>(())?;

    let domain_enc_output_ref = deps.require_ref::<DomainEnc>(task_key)?;
    let ty_constructor_enc_output_ref = deps.require_ref::<TyConstructorEnc>(task_key)?;

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl].into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        Some(vir::expr! {
            (acc_field([ref_field](ref_self)))
            && (([generic.param_type_function]([snap_data.value_access]([ref_field](ref_self)))) == ([generic_exprs[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function(
        "snap",
        &[ref_self_decl].into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        snap_type,
        &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
        &[vir::expr! { ([generic.param_type_function]([snap_data.value_access]([builder.vcx.mk_result(snap_type)]))) == ([generic_exprs[0]]) }],
        Some(vir::expr! {
            unfolding_wildcard ([self_pred](ref_self, ..[generic_exprs])) in ([ref_field](ref_self))
        }),
    ).1);

    // Ref-to-Ref
    let deref_func = builder.function(
        "deref",
        &[ref_self_decl].into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        &vir::TypeData::Ref,
        &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
        &[],
        Some(vir::expr! {
            unfolding_wildcard ([self_pred](ref_self, ..[generic_exprs])) in ([snap_data.deref_access]([ref_field](ref_self)))
        }),
    );

    let snap_self = builder.vcx.mk_local("snap", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    let snap_self_ex = builder.vcx.mk_local_ex_local(snap_self);

    let deref_ref = snap_data.deref_access.apply(builder.vcx, [snap_self_ex]);
    let deref_snap = snap_data.value_access.apply(builder.vcx, [snap_self_ex]);
    let deref_type = generic.param_type_function.apply(builder.vcx, [deref_snap]);

    let typeof_snap = domain_enc_output_ref.typeof_function.apply(builder.vcx, [snap_self_ex]);

    builder.get_unsafe_cells = Some(
        builder.mk_function(
            "get_all_UnsafeCells", 
            &[ref_self_decl, snap_self_decl].into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(), 
            builder.vcx.mk_ty_set(pair.pair_type), 
            &ty_constructor_enc_output_ref.ty_param_accessors
                    .iter()
                    .map(|f| f.apply(builder.vcx, [typeof_snap]))
                    .zip(generic_exprs.iter().cloned())
                    .map(|(lhs, rhs)| builder.vcx.mk_eq_expr(lhs, rhs))
                    .collect::<Vec<_>>(), 
            &[],
            Some(
                generic.get_unsafe_cells.apply(
                    builder.vcx, 
                    [deref_ref, deref_snap, deref_type],
                )
            )
        )
    );

    Ok((
        PredicateEncData::ImmRef(PredicateEncDataImmRef {
            deref_func: deref_func.to_known(),
            perm: None,
            snap_data,
        }),
        None,
    ))
}
