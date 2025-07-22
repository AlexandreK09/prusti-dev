use crate::encoders::{
    domain::{DomainBuilder, DomainDataStruct, DomainEnc, DomainEncSpecifics}, pair_ref_type::PairRefTypeOutputRef, predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataStruct}, snapshot::SnapshotEncOutput, PairRefTypeEnc, PredicateEnc
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert_eq!(*ty_kind, ty::TyKind::Str);

    let args0: &[_] = &[];
    let args1: &[_] = &[];
    let dummy_cons_ident = builder.function("cons", (args0, args1), builder.self_type());

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

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();
    let snap_data = snap.specifics.expect_structlike();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
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
            .mk_function::<vir::Ref, vir::CSnap>(
                "snap",
                ref_self_decl.ty(),
                //.into_iter()
                //    .chain(generic_decls.iter().cloned())
                //    .collect::<Vec<_>>(),
                snap_type,
                (ref_self_decl,),
                &[vir::expr! { acc([self_pred](ref_self, [])) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );

    let generic_tys: &[vir::Type<'vir, vir::TyVal>] = &[];
    let generic_decls: &[vir::LocalDecl<'vir, vir::TyVal>] = &[];

    builder.get_unsafe_cells = Some(
        builder
            .mk_function(
                "get_all_UnsafeCells", 
                (ref_self_decl.ty(), snap_self_decl.ty().upcast_ty(), generic_tys), 
                builder.vcx.mk_ty_set(vir::TYPE_PAIR), 
                (ref_self_decl, snap_self_decl.upcast_ty(), generic_decls),
                &[], 
                &[], 
                Some(builder.vcx.mk_set_literal_expr(&[], vir::TYPE_PAIR))
            )
    );

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(field_accessors.as_slice()),
    }))
}
