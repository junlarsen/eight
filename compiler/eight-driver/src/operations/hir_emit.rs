use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use crate::query::{EmitQuery, HirEmitQuery};
use eight_diagnostics::ice;
use eight_middle::hir::HirModule;
use eight_middle::passes::hir_textual_pass::{Document, HirModuleTextualPass};

/// Operation for emitting the HIR.
pub struct HirEmitPass;

impl HirEmitPass {
    pub fn decode<'c: 'p, 'p>(
        pipeline: &'c Pipeline<'c>,
        query: &HirEmitQuery,
        module: &'p HirModule<'c>,
        textual_pass: &'p HirModuleTextualPass<'p>,
    ) -> Result<Document<'p>, PipelineError> {
        match query {
            HirEmitQuery::Function(name) => {
                let name = pipeline.cc.intern_str(name);
                let function = module
                    .body
                    .functions
                    .get(&name)
                    .unwrap_or_else(|| ice!("function {} not found", name));
                Ok(textual_pass.visit_function(function))
            }
        }
    }
}

impl<'hir> PipelinePass<'hir, HirModule<'hir>, HirModule<'hir>> for HirEmitPass {
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
            eprintln!("{}", text);
            return Ok(input);
        }
        // Otherwise, we emit the results of the queries.
        for query in pipeline.opts.queries.iter() {
            let EmitQuery::Hir(query) = query else {
                continue;
            };
            let target = Self::decode(pipeline, query, &input, &textual_pass)?;
            let text = HirModuleTextualPass::format_doc_to_string(target);
            eprintln!("{}", text);
        }
        Ok(input)
    }
}
