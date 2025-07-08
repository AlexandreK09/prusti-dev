use crate::encoders::{
    domain::{DomainBuilder, DomainDataStruct, DomainEnc, DomainEncSpecifics}, pair_ref_type::PairRefTypeOutputRef, predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataStruct}, snapshot::SnapshotEncOutput, PairRefTypeEnc, PredicateEnc
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert_eq!(*ty_kind, ty::TyKind::Str);

    let dummy_cons_ident = builder.function("cons", &[], builder.self_type());

    Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
        field_snaps_to_snap: dummy_cons_ident,
        field_access: &[],
    }))
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    pair: &PairRefTypeOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();
    // let ty::TyKind::Str = ty_kind else { unreachable!(); };

    let snap_type = snap.snapshot;
    let snap_data = snap.specifics.expect_structlike();

    //let snap_self = builder.vcx.mk_local("self", snap_type);
    //let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    //let snap_self_ex: vir::Expr = builder.vcx.mk_local_ex_local(snap_self);

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let snap_self = builder.vcx.mk_local("snap", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);

    let (field_accessors, self_pred, snap_expr, _) = super::structlike::predicate(
        "",
        &[],
        snap_data.field_access,
        task_key,
        &snap,
        pair,
        snap_data.field_snaps_to_snap,
        deps,
        &[],
        &[],
        builder,
    )?;

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function(
                "snap",
                &[ref_self_decl],
                //.into_iter()
                //    .chain(generic_decls.iter().cloned())
                //    .collect::<Vec<_>>(),
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );

    let pair_ref_type = deps.require_ref::<PairRefTypeEnc>(())?;

    builder.get_unsafe_cells = Some(
        builder
            .mk_function(
                "get_all_UnsafeCells", 
                &[ref_self_decl, snap_self_decl], 
                builder.vcx.mk_ty_set(pair.pair_type), 
                &[], 
                &[], 
                Some(
                    vir::expr! {
                        Set([pair_ref_type.pair_type]())
                    }
                )
            )
    );

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors),
    }))
}
