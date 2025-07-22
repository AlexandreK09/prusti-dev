use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{CastType, Domain, DomainGenData, FunctionIdn, TypeData, ViperIdent};

use crate::encoders::GenericEnc;

pub struct PairRefTypeEnc;

#[derive(Debug, Clone)]
pub enum PairRefTypeEncError{}

#[derive(Clone)]
pub struct PairRefTypeOutputRef<'vir>{
    pub constructor: FunctionIdn<'vir, (vir::Ref, vir::TyVal), vir::PairRefType>,
    pub type_accessor: FunctionIdn<'vir, (vir::PairRefType), vir::TyVal>,
    pub ref_accessor: FunctionIdn<'vir, (vir::PairRefType), vir::Ref>
}

impl<'vir> OutputRefAny for PairRefTypeOutputRef<'vir>{}

#[derive(Clone)]
pub struct PairRefTypeOutput<'vir>{
    pub domain: Domain<'vir>
}

pub const DOMAIN_NAME: &'static str = "Pair_Ref_Type";

impl TaskEncoder for PairRefTypeEnc {
    task_encoder::encoder_cache!(PairRefTypeEnc);

    type TaskDescription<'vir> = ();

    type OutputRef<'vir> = PairRefTypeOutputRef<'vir>;

    type OutputFullLocal<'vir> = PairRefTypeOutput<'vir>;

    type EncodingError = PairRefTypeEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let generic_enc_output_ref = deps.require_ref::<GenericEnc>(())?;

        let (constructor, type_accessor, ref_accessor) = vir::with_vcx(|vcx|{
            let constructor_id = FunctionIdn::new(
                ViperIdent::new("pair_ref_type"), 
                (vir::TYPE_REF, vir::TYPE_TYVAL), 
                vir::TYPE_PAIR
            );
            let constructor = (constructor_id, vcx.mk_domain_function(constructor_id, false));

            let type_id = FunctionIdn::new(
                ViperIdent::new("pair_ref_type_type"),
                (vir::TYPE_PAIR),
                vir::TYPE_TYVAL
            );
            let type_accessor = (type_id, vcx.mk_domain_function(type_id, false));

            let ref_id = FunctionIdn::new(
                ViperIdent::new("pair_ref_type_ref"), 
                (vir::TYPE_PAIR), 
                vir::TYPE_REF
            );
            let ref_accessor = (ref_id, vcx.mk_domain_function(ref_id, false));

            (constructor, type_accessor, ref_accessor)
        });

        deps.emit_output_ref(
            *task_key, 
            PairRefTypeOutputRef{
                constructor: constructor.0, 
                type_accessor: type_accessor.0, 
                ref_accessor: ref_accessor.0 
            }
        )?;

        let domain = vir::with_vcx(|vcx| {
            let functions = vcx.alloc_slice(&[constructor.1, type_accessor.1, ref_accessor.1]);

            let axioms = vcx.alloc_slice(&[
                vcx.mk_domain_axiom(
                    ViperIdent::new("pair_ref_type_ax_ref"),
                    vir::expr!{
                        forall r: [vir::TYPE_REF], t: [generic_enc_output_ref.type_snapshot] ::
                        {[constructor.0](r, t)}
                        ([ref_accessor.0]([constructor.0](r, t))) == (r)
                    }
                ),
                vcx.mk_domain_axiom(
                    ViperIdent::new("pair_ref_type_ax_type"),
                    vir::expr!{
                        forall r: [vir::TYPE_REF], t: [generic_enc_output_ref.type_snapshot] ::
                        {[constructor.0](r, t)}
                        ([type_accessor.0]([constructor.0](r, t))) == (t)
                    }
                ),
                vcx.mk_domain_axiom(
                    ViperIdent::new("pair_ref_type_ax_inj"), 
                    {
                        let p = vcx.mk_local_decl("p", vir::TYPE_PAIR);
                        let p_ex = vcx.mk_local_ex("p", vir::TYPE_PAIR);
                        let r = vir::expr!{ [ref_accessor.0](p_ex) };
                        let t = vir::expr!{ [type_accessor.0](p_ex) };
                        vcx.mk_forall_expr(
                            vcx.alloc_slice(&[p]), 
                            vcx.alloc_slice(&[vcx.mk_trigger(vcx.alloc_slice(&[r.as_dyn(), t.as_dyn()]))]), 
                            vcx.mk_eq_expr(constructor.0.gen()(r, t), p_ex)
                        )
                        /*vir::expr!{
                            forall p: [vir::TYPE_PAIR]::
                            {r, t}
                            ([constructor.0](r, t)) == (p)
                        }*/
                    }
                )
            ]);
            vcx.alloc(DomainGenData{
                name: DOMAIN_NAME,
                typarams: &[],
                axioms,
                functions
            })
        });

        Ok((PairRefTypeOutput{domain}, ()))
    }
}