use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{vir_format_identifier, CallableIdent, DomainAxiomData, DomainAxiomGen, DomainAxiomGenData, FunctionIdent, UnaryArity, UnknownArity, VirCtxt};

use crate::encoders::{
    most_generic_ty::{extract_type_params, MostGenericTy},
    GenericEnc,
};

#[derive(Clone)]
pub struct TyConstructorEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub ty_constructor: vir::FunctionIdent<'vir, UnknownArity<'vir>>,

    /// Accessors of the arguments to an instantiation of the type constructor.
    /// Each function takes as input an instantiated type. The `i`th function in
    /// this list returns the `i`th argument to the type constructor.
    pub ty_param_accessors: &'vir [vir::FunctionIdent<'vir, UnaryArity<'vir>>],
    
    pub is_ty: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> TyConstructorEncOutputRef<'vir> {
    pub fn arity(&self) -> UnknownArity<'vir> {
        *self.ty_constructor.arity()
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct TyConstructorEncOutput<'vir> {
    pub domain: vir::Domain<'vir>,
    pub constructor_ident: FunctionIdent<'vir, UnknownArity<'vir>>,
}

impl<'vir> TyConstructorEncOutput<'vir> {
    pub fn disjoint_type<Curr, Next>(&self, other: &TyConstructorEncOutput<'vir>, vcx: &'vir VirCtxt, type_t: &'vir vir::TypeData<'vir>) -> DomainAxiomGen<'vir, Curr, Next>{
        let typarams_count_self = self.constructor_ident.arity().len();
        let typarams_count_other = other.constructor_ident.arity().len();
        let locals_self = (0..typarams_count_self).map(|i| vcx.mk_local(&vir::vir_format!(vcx, "t{}", i), type_t)).collect::<Vec<_>>();
        let locals_other = (typarams_count_self..typarams_count_self+typarams_count_other).map(|i| vcx.mk_local(&vir::vir_format!(vcx, "t{}", i), type_t)).collect::<Vec<_>>();

        let self_app = self.constructor_ident.apply(vcx, vcx.alloc_slice(&locals_self.iter().map(|local| vcx.mk_local_ex_local(local)).collect::<Vec<_>>()));
        let other_app = other.constructor_ident.apply(vcx, vcx.alloc_slice(&locals_other.iter().map(|local| vcx.mk_local_ex_local(local)).collect::<Vec<_>>()));

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
            vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, self_app, other_app)
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
            let type_function_ident = FunctionIdent::new(
                vir::vir_format_identifier!(
                    vcx,
                    "s_{}_type",
                    ty_constructor.get_vir_base_name(vcx)
                ),
                UnknownArity::new(type_function_args),
                generic_ref.type_snapshot,
            );
            functions.push(vcx.mk_domain_function(type_function_ident, args.len() == 0));
            let ty_arg_decls: Vec<vir::LocalDecl<'vir>> = args
                .iter()
                .enumerate()
                .map(|(idx, _)| {
                    vcx.mk_local_decl(
                        vcx.alloc_str(&format!("arg_{}", idx)),
                        generic_ref.type_snapshot,
                    )
                })
                .collect();
            let ty_arg_exprs: Vec<vir::Expr<'vir>> = ty_arg_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
                .collect::<Vec<_>>();
            let func_app = type_function_ident.apply(vcx, &ty_arg_exprs);

            let ty_accessor_args = vcx.alloc_array(&[generic_ref.type_snapshot]);
            let ty_accessor_functions = args
                .iter()
                .map(|arg| {
                    FunctionIdent::new(
                        vir::vir_format_identifier!(
                            vcx,
                            "s_{}_typaram_{}",
                            ty_constructor.get_vir_base_name(vcx),
                            arg.name
                        ),
                        UnaryArity::new(ty_accessor_args),
                        generic_ref.type_snapshot,
                    )
                })
                .collect::<Vec<_>>();

            let is_ty_args = vcx.alloc_array(&[generic_ref.type_snapshot]);
            let is_ty_ident = FunctionIdent::new(
                vir::vir_format_identifier!(
                    vcx,
                    "is_s_{}_type",
                    ty_constructor.get_vir_base_name(vcx)
                ),
                UnaryArity::new(is_ty_args),
                &vir::TypeData::Bool
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
                        vcx.mk_eq_expr(accessor_function.apply(vcx, [func_app]), ty_arg),
                    ),
                ))
            }
            axioms.push(vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "ax_is_s_{}_type", ty_constructor.get_vir_base_name(vcx)),
                vcx.mk_forall_expr(
                    axiom_qvars, 
                    axiom_triggers, 
                    is_ty_ident.apply(vcx, [func_app]),
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
                        is_ty_ident.apply(vcx, [t_expr]), 
                        vcx.mk_eq_expr(
                            t_expr, 
                            type_function_ident.apply(
                                vcx, 
                                vcx.alloc_slice(&ty_accessor_functions.iter()
                                    .map(|accessor|
                                        accessor.apply(vcx, [t_expr])
                                    )
                                    .collect::<Vec<_>>()
                                )
                            )
                        )
                    )
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
