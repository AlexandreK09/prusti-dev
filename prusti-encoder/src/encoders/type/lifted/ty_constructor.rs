use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{vir_format_identifier, Arity, CallableIdn, CastType, DomainAxiomGen, FunctionIdn, VirCtxt};

use crate::encoders::{
    most_generic_ty::{extract_type_params, MostGenericTy},
    GenericEnc,
};

#[derive(Clone)]
pub struct TyConstructorEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub ty_constructor: vir::FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>,

    /// Accessors of the arguments to an instantiation of the type constructor.
    /// Each function takes as input an instantiated type. The `i`th function in
    /// this list returns the `i`th argument to the type constructor.
    pub ty_param_accessors: &'vir [vir::FunctionIdn<'vir, vir::TyVal, vir::TyVal>],
    
    pub is_ty: vir::FunctionIdn<'vir, vir::TyVal, vir::Bool>,
}

impl<'vir> TyConstructorEncOutputRef<'vir> {
    pub fn arity(&self) -> <vir::ManyTyVal as Arity>::Tys<'vir> {
        self.ty_constructor.arity()
    }

    pub fn args(&self) -> impl Iterator<Item = vir::TypeTyVal<'vir>> + '_ {
        self.arity().into_iter().copied()
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct TyConstructorEncOutput<'vir> {
    pub domain: vir::Domain<'vir>,
    pub constructor_ident: FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>,
}

impl<'vir> TyConstructorEncOutput<'vir> {
    pub fn disjoint_type<Curr, Next>(&self, other: &TyConstructorEncOutput<'vir>, vcx: &'vir VirCtxt) -> DomainAxiomGen<'vir, Curr, Next>{
        let typarams_count_self = self.constructor_ident.arity().len();
        let typarams_count_other = other.constructor_ident.arity().len();
        let locals_self = (0..typarams_count_self).map(|i| vcx.mk_local(&vir::vir_format!(vcx, "t{}", i), vir::TYPE_TYVAL)).collect::<Vec<_>>();
        let locals_other = (typarams_count_self..typarams_count_self+typarams_count_other).map(|i| vcx.mk_local(&vir::vir_format!(vcx, "t{}", i), vir::TYPE_TYVAL)).collect::<Vec<_>>();

        let self_app = self.constructor_ident.gen()(vcx.alloc_slice(&locals_self.iter().map(|local| vcx.mk_local_ex_local(local)).collect::<Vec<_>>()));
        let other_app = other.constructor_ident.gen()(vcx.alloc_slice(&locals_other.iter().map(|local| vcx.mk_local_ex_local(local)).collect::<Vec<_>>()));

        let qvars = vcx.alloc_slice(&locals_self.iter().chain(locals_other.iter()).map(|local| vcx.mk_local_decl_local(local)).collect::<Vec<_>>());
        let mut triggers_list = Vec::new();
        if typarams_count_self > 0{
            triggers_list.push(self_app);
        }
        if typarams_count_other > 0{
            triggers_list.push(other_app);
        }
        let triggers = vcx.alloc_slice(&[vcx.mk_trigger(vcx.alloc_slice(&triggers_list))]);

        let forall = vcx.mk_forall_expr(
            qvars, 
            triggers, 
            vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, self_app, other_app).downcast_ty()
        );

        vcx.mk_domain_axiom(
            vir::vir_format_identifier!(vcx, "ax_disjoint_{}_{}", self.domain.name, other.domain.name), 
            forall
        )
    }
}

/// Encodes the lifted representation of a Rust type constructor (e.g. Option,
/// Vec, user-defined ADTs).
pub struct TyConstructorEnc;

impl TaskEncoder for TyConstructorEnc {
    task_encoder::encoder_cache!(TyConstructorEnc);
    type TaskDescription<'tcx> = MostGenericTy<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = TyConstructorEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = TyConstructorEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let generic_ref = deps.require_ref::<GenericEnc>(())?;
        let mut functions = vec![];
        let mut axioms = vec![];
        vir::with_vcx(|vcx| {
            let (ty_constructor, _) = extract_type_params(vcx.tcx(), task_key.ty());
            let args = ty_constructor.generics();
            let type_function_args = vcx.alloc_slice(&vec![generic_ref.type_snapshot; args.len()]);
            let type_function_ident = FunctionIdn::new(
                vir::vir_format_identifier!(
                    vcx,
                    "s_{}_type",
                    ty_constructor.get_vir_base_name(vcx)
                ),
                type_function_args,
                generic_ref.type_snapshot,
            );
            functions.push(vcx.mk_domain_function(type_function_ident, false));
            let ty_arg_decls: Vec<vir::LocalDeclTyVal<'vir>> = args
                .iter()
                .enumerate()
                .map(|(idx, _)| {
                    vcx.mk_local_decl(
                        vcx.alloc_str(&format!("arg_{}", idx)),
                        generic_ref.type_snapshot,
                    )
                })
                .collect();
            let ty_arg_exprs: Vec<vir::ExprTyVal<'vir>> = ty_arg_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
                .collect::<Vec<_>>();
            let func_app = type_function_ident(ty_arg_exprs.as_slice());

            let ty_accessor_functions = args
                .iter()
                .map(|arg| {
                    FunctionIdn::new(
                        vir::vir_format_identifier!(
                            vcx,
                            "s_{}_typaram_{}",
                            ty_constructor.get_vir_base_name(vcx),
                            arg.name
                        ),
                        generic_ref.type_snapshot,
                        generic_ref.type_snapshot,
                    )
                })
                .collect::<Vec<_>>();

            let is_ty_ident = FunctionIdn::new(
                vir::vir_format_identifier!(
                    vcx,
                    "is_s_{}_type",
                    ty_constructor.get_vir_base_name(vcx)
                ),
                generic_ref.type_snapshot,
                vir::TYPE_BOOL
            );
            functions.push(vcx.mk_domain_function(is_ty_ident, false));
            deps.emit_output_ref(
                *task_key,
                TyConstructorEncOutputRef {
                    ty_constructor: type_function_ident,
                    ty_param_accessors: vcx.alloc_slice(&ty_accessor_functions),
                    is_ty: is_ty_ident
                },
            )?;

            let axiom_qvars = vcx.alloc_slice(&ty_arg_decls);
            let axiom_triggers = vcx.alloc_slice(&[vcx.mk_trigger(&[func_app])]);
            for (accessor_function, ty_arg) in ty_accessor_functions.iter().zip(ty_arg_exprs.iter())
            {
                functions.push(vcx.mk_domain_function(*accessor_function, false));
                axioms.push(vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(vcx, "ax_{}", accessor_function.name()),
                    vcx.mk_forall_expr(
                        axiom_qvars,
                        axiom_triggers,
                        vcx.mk_eq_expr(accessor_function(func_app), ty_arg),
                    ),
                ))
            }
            axioms.push(vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "ax_is_s_{}_type", ty_constructor.get_vir_base_name(vcx)),
                vcx.mk_forall_expr(
                    axiom_qvars, 
                    axiom_triggers, 
                    is_ty_ident.gen()(func_app),
                ))
            );
            let t_local = vcx.mk_local("t", generic_ref.type_snapshot);
            let t_expr = vcx.mk_local_ex_local(t_local);
            let axiom_inv_qvars = vcx.alloc_slice(&[vcx.mk_local_decl_local(t_local)]);
            axioms.push(vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "ax_s_{}_type_inv", ty_constructor.get_vir_base_name(vcx)),
                vcx.mk_forall_expr(
                    axiom_inv_qvars,
                    &[],
                    vcx.mk_bin_op_expr(vir::BinOpKind::Implies, 
                        is_ty_ident.gen()(t_expr), 
                        vcx.mk_eq_expr(
                            t_expr, 
                            type_function_ident.gen()(
                                vcx.alloc_slice(&ty_accessor_functions.iter()
                                    .map(|accessor|
                                        accessor.gen()(t_expr)
                                    )
                                    .collect::<Vec<_>>()
                                )
                            )
                        )
                    ).downcast_ty()
                ))
            );
            let result = TyConstructorEncOutput {
                domain: vcx.mk_domain(
                    vir_format_identifier!(
                        vcx,
                        "s_{}_ty_constructor",
                        task_key.get_vir_base_name(vcx)
                    ),
                    &[],
                    vcx.alloc_slice(&axioms),
                    vcx.alloc_slice(&functions),
                ),
                constructor_ident: type_function_ident
            };
            Ok((result, ()))
        })
    }
}
