use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use crate::query::{EmitQuery, HirEmitQuery};
use eight_diagnostics::ice;
use eight_hir::textual_pass::{Document, HirModuleTextualPass};
use eight_hir::HirModule;

/// Operation for emitting the HIR.
pub struct HirEmitOperation;

impl HirEmitOperation {
    pub fn decode<'hir: 'a, 'a>(
        pipeline: &'hir Pipeline<'hir>,
        query: &HirEmitQuery,
        module: &'a HirModule<'hir>,
        textual_pass: &'a HirModuleTextualPass<'a>,
    ) -> Result<Document<'a>, PipelineError> {
        match query {
            HirEmitQuery::Function(name) => {
                // TODO: This shouldn't really happen...
                let name = pipeline.hir_arena.names().get(name);
                let function = module
                    .body
                    .functions
                    .get(&name)
                    .unwrap_or_else(|| ice!(format!("function {} not found", name)));
                Ok(textual_pass.visit_function(function))
            }
        }
    }
}

impl<'hir> PipelineOperation<'hir, HirModule<'hir>, HirModule<'hir>> for HirEmitOperation {
    fn execute(
        pipeline: &'hir Pipeline<'hir>,
        input: HirModule<'hir>,
    ) -> Result<HirModule<'hir>, PipelineError> {
        if !pipeline.opts.emit_hir {
            return Ok(input);
        }
        let textual_pass = HirModuleTextualPass::default();
        // If no query patterns have been specified, we dump the entire module.
        if pipeline.opts.queries.is_empty() {
            let text =
                HirModuleTextualPass::format_doc_to_string(textual_pass.visit_module(&input));
            println!("{}", text);
            return Ok(input);
        }
        // Otherwise, we emit the results of the queries.
        for query in pipeline.opts.queries.iter() {
            let EmitQuery::Hir(query) = query else {
                continue;
            };
            let target = Self::decode(pipeline, query, &input, &textual_pass)?;
            let text = HirModuleTextualPass::format_doc_to_string(target);
            println!("{}", text);
        }
        Ok(input)
    }
}
