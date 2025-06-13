use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{BinaryArity, CallableIdent, Domain, DomainGenData, DomainIdent, FunctionIdent, Type, TypeData, UnaryArity, UnknownArityAny, ViperIdent};

use crate::encoders::GenericEnc;

pub struct PairRefTypeEnc;

#[derive(Debug, Clone)]
pub enum PairRefTypeEncError{}

#[derive(Clone)]
pub struct PairRefTypeOutputRef<'vir>{
    pub pair_type: Type<'vir>,
    pub constructor: FunctionIdent<'vir, BinaryArity<'vir>>,
    pub type_accessor: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub ref_accessor: FunctionIdent<'vir, UnaryArity<'vir>>
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

        let (constructor, type_accessor, ref_accessor, pair_type) = vir::with_vcx(|vcx|{
            let id = DomainIdent::new(ViperIdent::new(DOMAIN_NAME), UnknownArityAny::new(&[]));
            let pair_type = vir::with_vcx(|vcx|
                id.apply(vcx, &[])
            );

            let constructor_args = vcx.alloc_array(&[&TypeData::Ref, generic_enc_output_ref.type_snapshot]);
            let constructor_id = FunctionIdent::new(
                ViperIdent::new("pair_ref_type"), 
                BinaryArity::new(constructor_args), 
                pair_type
            );
            let constructor = (constructor_id, vcx.mk_domain_function(constructor_id, false));
            
            let type_args = vcx.alloc_array(&[pair_type]);
            let type_id = FunctionIdent::new(
                ViperIdent::new("pair_ref_type_type"),
                UnaryArity::new(type_args),
                generic_enc_output_ref.type_snapshot
            );
            let type_accessor = (type_id, vcx.mk_domain_function(type_id, false));

            let ref_args = vcx.alloc_array(&[pair_type]);
            let ref_id = FunctionIdent::new(
                ViperIdent::new("pair_ref_type_ref"), 
                UnaryArity::new(ref_args), 
                &TypeData::Ref
            );
            let ref_accessor = (ref_id, vcx.mk_domain_function(ref_id, false));

            (constructor, type_accessor, ref_accessor, pair_type)
        });

        deps.emit_output_ref(
            *task_key, 
            PairRefTypeOutputRef{ 
                pair_type,
                constructor: constructor.0, 
                type_accessor: type_accessor.0, 
                ref_accessor: ref_accessor.0 
            }
        )?;

        let domain = vir::with_vcx(|vcx| {
            let functions = vcx.alloc_slice(&[constructor.1, type_accessor.1, ref_accessor.1]);
            vcx.alloc(DomainGenData{
                name: DOMAIN_NAME,
                typarams: &[],
                axioms: &[],
                functions
            })
        });

        Ok((PairRefTypeOutput{domain}, ()))
    }
}