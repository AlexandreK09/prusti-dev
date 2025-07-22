use crate::encoders::{domain::{DomainBuilder, DomainEnc, DomainEncSpecifics}, predicate::{PredicateBuilder}, snapshot::SnapshotEncOutput};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{HasType, PredicateIdn};

pub(crate) fn domain<'vir>(
    _task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    Ok(DomainEncSpecifics::Opaque)
}

pub(crate) fn predicate<'vir>(
    snap: SnapshotEncOutput<'vir>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> PredicateIdn<'vir, (vir::Ref, vir::Many<vir::TyVal>)>
{
    let snap_type = snap.snapshot;

    let generic_tys = generic_decls
        .iter()
        .copied()
        .map(vir::LocalDeclData::ty)
        .collect::<Vec<_>>();
    let generic_tys = builder.vcx.alloc_slice(&generic_tys);

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    let self_pred = builder.predicate::<(vir::Ref, vir::ManyTyVal)>(
        "", 
        (ref_self_decl.ty(), generic_tys),
        (ref_self_decl, generic_decls), 
        None
    );

    builder.function_snap = Some(
        builder
        .mk_function::<(vir::Ref, vir::ManyTyVal), vir::Snap>(
            "snap",
            (ref_self_decl.ty(), generic_tys),
            snap_type,
            (ref_self_decl, generic_decls),
            &[vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) }],
            &[],
            None
        )
        .1,
    );
    self_pred
}
