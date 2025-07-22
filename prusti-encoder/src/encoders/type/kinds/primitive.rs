use crate::encoders::{
    domain::{DomainBuilder, DomainDataPrim, DomainEnc, DomainEncSpecifics}, lifted::ty_constructor::TyConstructorEnc, pair_ref_type::PairRefTypeOutputRef, predicate::{PredicateBuilder, PredicateEncData, RefToIndirectPred}, snapshot::SnapshotEncOutput, PredicateEnc
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, HasType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    typeof_ident: FunctionIdn<'vir, vir::CSnap, vir::TyVal>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let prim_type: vir::TypePrim<'vir> = match ty_kind {
        ty::TyKind::Bool => vir::TYPE_BOOL.upcast_ty(),
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::TYPE_INT.upcast_ty(),
        ty::TyKind::Float(_) => todo!(),
        _ => unreachable!(),
    };

    let value_ident = builder.function("value", builder.self_type(), prim_type);
    let cons_ident = builder.function("cons", prim_type, builder.self_type());

    builder.axiom("cons", vir::expr! {
        forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
    });

    let ty_constr = deps.require_ref::<TyConstructorEnc>(task_key)?;

    builder.axiom(
        "type",
        vir::expr! {
            forall value: [prim_type] :: {[cons_ident](value)} ([typeof_ident]([cons_ident](value))) == ([ty_constr.ty_constructor]([]))
        },
    );

    match ty_kind {
        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
            let min = builder.vcx.get_min_int(&ty_kind);
            let max = builder.vcx.get_max_int(&ty_kind);
            builder.axiom("bounds", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= (([value_ident](s)) as Int)) && ((([value_ident](s)) as Int) <= ([max]))
            });
            builder.axiom(
                "value",
                vir::expr! {
                    forall value: [prim_type] :: {[cons_ident](value)}
                        ((([min]) <= ((value) as Int)) && (((value) as Int) <= ([max])))
                            ==> (([value_ident]([cons_ident](value))) == (value))
                },
            );
        }
        _ => {
            builder.axiom("value", vir::expr! {
                forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
            });
        }
    };

    Ok(DomainEncSpecifics::Primitive(DomainDataPrim {
        prim_type,
        snap_to_prim: value_ident,
        prim_to_snap: cons_ident,
    }))
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    pair: &PairRefTypeOutputRef<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (PredicateEncData<'vir>, Option<RefToIndirectPred<'vir>>),
    EncodeFullError<'vir, PredicateEnc>,
> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    let snap_self = builder.vcx.mk_local("snap", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);

    // fields
    let prim_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { acc((ref_self).[prim_field]) }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<vir::Ref, _>(
                "snap",
                ref_self_decl.ty(),
                snap_type,
                (ref_self_decl,),
                &[vir::expr! { acc([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding ([self_pred](ref_self)) in ([prim_field](ref_self))
                }),
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

    Ok((
        PredicateEncData::Primitive(snap.specifics.expect_primitive()),
        None,
    ))
}
