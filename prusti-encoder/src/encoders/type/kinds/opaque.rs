use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncSpecifics}, 
    predicate::PredicateBuilder, 
    snapshot::SnapshotEncOutput
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{PredicateIdent};

pub(crate) fn domain<'vir>(
    _task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    Ok(DomainEncSpecifics::Opaque)
}

pub(crate) fn predicate<'vir>(
    snap: SnapshotEncOutput<'vir>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> PredicateIdent<'vir, vir::UnknownArity<'vir>>
{
    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    let args = &[ref_self_decl]
        .into_iter()
        .chain(generic_decls.iter().cloned())
        .collect::<Vec<_>>();
    let self_pred = builder.predicate("", &args, None);

    builder.function_snap = Some(
        builder
        .mk_function(
            "snap",
            &args,
            snap_type,
            &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
            &[],
            None
        )
        .1,
    );
    self_pred
}
