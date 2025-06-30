#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(let_chains)] 
#![feature(box_patterns)]
#![feature(never_type)]
#![allow(clippy::needless_lifetimes)]

mod encoders;
mod encoder_traits;
pub mod request;

use prusti_interface::{environment::EnvBody, PrustiError};
use prusti_rustc_interface::{hir, middle::ty};
use task_encoder::TaskEncoder;
use vir::{with_vcx, ViperIdent};

use crate::encoders::{
    lifted::{
        casters::{CastTypeImpure, CastTypePure, CastersEnc},
        ty_constructor::TyConstructorEnc,
    },
    MirPolyImpureEnc,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> request::RequestWithContext {
    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir().body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                    let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                    let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                    (is_pure, is_trusted)
                })
                .unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let res = MirPolyImpureEnc::encode(def_id, false);
                    assert!(res.is_ok());
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    fn header(code: &mut String, title: &str) {
        code.push_str("// -----------------------------\n");
        code.push_str(&format!("// {}\n", title));
        code.push_str("// -----------------------------\n");
    }
    let mut viper_code = String::new();

    let mut program_fields = vec![];
    let mut program_domains = vec![];
    let mut program_predicates = vec![];
    let mut program_functions = vec![];
    let mut program_methods = vec![];

    // We output results from both monomorphic and polymorphic encoding of
    // functions, because even when Prusti is configured to use the monomorphic
    // it will still use `MirPolyImpureEnc` directly sometimes (see usages
    // earlier in this file).
    header(&mut viper_code, "methods");
    for output in crate::encoders::MirMonoImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        program_methods.push(output.method);
    }
    for output in crate::encoders::MirPolyImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        program_methods.push(output.method);
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::PureFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.type_snapshot));
        viper_code.push_str(&format!("{:?}\n", output.param_snapshot));
        program_domains.push(output.type_snapshot);
        program_domains.push(output.param_snapshot);
    }


    header(&mut viper_code, "pair");
    
    for output in crate::encoders::PairRefTypeEnc::all_outputs(){
        viper_code.push_str(&format!("{:?}\n", output.domain));
        program_domains.push(output.domain);
    }

    header(&mut viper_code, "pure generic casts");
    for cast_functions in CastersEnc::<CastTypePure>::all_outputs() {
        for cast_function in cast_functions {
            viper_code.push_str(&format!("{:?}\n", cast_function));
            program_functions.push(cast_function);
        }
    }

    header(&mut viper_code, "impure generic casts");
    for cast_methods in CastersEnc::<CastTypeImpure>::all_outputs() {
        for cast_method in cast_methods {
            viper_code.push_str(&format!("{:?}\n", cast_method));
            program_methods.push(cast_method);
        }
    }

    header(&mut viper_code, "snapshots");
    for output in crate::encoders::DomainEnc_all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output));
        program_domains.push(output);
    }

    header(&mut viper_code, "type constructors");

    let mut type_constructors = Vec::new();

    for output in TyConstructorEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.domain));
        program_domains.push(output.domain);

        type_constructors.push(output);
    }

    let type_disjunction = vir::with_vcx(|vcx|{
        let mut axioms = Vec::new();
        for i in 0..type_constructors.len(){
            for j in i+1..type_constructors.len(){
                axioms.push(type_constructors[i].disjoint_type(&type_constructors[j], vcx, &vir::TypeData::Domain("Type", &[])));
            }
        }
        vcx.mk_domain(
            ViperIdent::new("type_disjunction"), 
            &[], 
            vcx.alloc_slice(&axioms), 
            &[]
        )
    });

    viper_code.push_str(&format!("{:?}\n", type_disjunction));
    program_domains.push(type_disjunction);

    header(&mut viper_code, "types");

    let mut p_param_body_elements = Vec::new();
    let mut p_param_body = None;
    let mut p_param_get_unsafe_cells_unknown = None;

    for output in crate::encoders::PredicateEnc::all_outputs() {
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
            program_fields.push(field);
        }
        for field_projection in output.ref_to_field_refs {
            viper_code.push_str(&format!("{:?}", field_projection));
            program_functions.push(field_projection);
        }
        viper_code.push_str(&format!("{:?}\n", output.unreachable_to_snap));
        program_functions.push(output.unreachable_to_snap);
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        program_functions.push(output.function_snap);
        viper_code.push_str(&format!("{:?}\n", output.get_unsafe_cells));
        program_functions.push(output.get_unsafe_cells);
        for pred in output.predicates {
            viper_code.push_str(&format!("{:?}\n", pred));
            program_predicates.push(pred);
        }
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
        program_methods.push(output.method_assign);
        if let Some(body) = output.param_get_unsafe_cell_body{
            if let Some(cond) = output.param_get_unsafe_cell_condition{
                p_param_body_elements.push((body, cond));
            }else{
                p_param_body = Some(body);
                p_param_get_unsafe_cells_unknown = Some(output.get_unsafe_cells);
            }
        }
    }

    if let Some(body) = vir::with_vcx(|vcx| p_param_body.map(|init| p_param_body_elements.iter().fold(init, |acc, current| vcx.mk_ternary_expr(current.1, current.0, acc)))) {
        let unknown  = p_param_get_unsafe_cells_unknown.unwrap();
        let param_get_unsafe_cells = with_vcx(|vcx|{
            vcx.mk_function(
                "p_Param_get_all_UnsafeCells", 
                unknown.args,
                unknown.ret,
                unknown.pres,
                unknown.posts,
                Some(body)
            )
        });
        program_functions.push(param_get_unsafe_cells);
        viper_code.push_str(&format!("{:?}\n", param_get_unsafe_cells));
    }

    if std::env::var("LOCAL_TESTING").is_ok() {
        std::fs::write("local-testing/simple.vpr", viper_code).unwrap();
    }

    let program = vir::with_vcx(|vcx| {
        vcx.mk_program(
            vcx.alloc_slice(&program_fields),
            vcx.alloc_slice(&program_domains),
            vcx.alloc_slice(&program_predicates),
            vcx.alloc_slice(&program_functions),
            vcx.alloc_slice(&program_methods),
        )
    });

    /*
    let source_path = std::path::Path::new("source/path"); // TODO: env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    */

    request::RequestWithContext {
        program: program.to_ref(),
    }
}

pub fn backtranslate_error(
    error_kind: &str,
    offending_pos_id: usize,
    reason_pos_id: Option<usize>,
) -> Option<Vec<PrustiError>> {
    vir::with_vcx(|vcx| vcx.backtranslate(error_kind, offending_pos_id, reason_pos_id))
}
