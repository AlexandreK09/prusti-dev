use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncSpecifics}, pair_ref_type::{PairRefTypeOutputRef}, predicate::{PredicateBuilder, PredicateEncData}, snapshot::SnapshotEncOutput, PairRefTypeEnc, PredicateEnc
};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    assert_eq!(*task_key.ty().kind(), ty::TyKind::Never);
    Ok(DomainEncSpecifics::Never)
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    pair: &PairRefTypeOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    // main predicate
    let self_pred = builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { false }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<vir::Ref, _>(
                "snap",
                ref_self_decl.ty(),
                snap_type,
                (ref_self_decl,),
                &[], // &[vir::expr! { false }],
                &[],
                None,
            )
            .1,
    );

    let snap_self = builder.vcx.mk_local("snap", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);

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

    Ok(PredicateEncData::Never)
}
