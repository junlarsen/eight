use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use crate::query::{EmitQuery, MirEmitQuery};
use eight_diagnostics::ice;
use eight_middle::mir::module::MirModule;
use eight_middle::passes::mir_textual_pass::{Document, MirModuleTextualPass};

pub struct MirEmitPass {}

impl MirEmitPass {
    pub fn decode<'c: 'p, 'p>(
        pipeline: &'c Pipeline<'c>,
        query: &MirEmitQuery,
        module: &'p MirModule<'p>,
        textual_pass: &'p MirModuleTextualPass<'p>,
    ) -> Result<Document<'p>, PipelineError> {
        match query {
            MirEmitQuery::Function(name) => {
                let name = pipeline.cc.intern_str(name);
                let function = module
                    .data()
                    .get_function(name)
                    .unwrap_or_else(|| ice!("function {} not found", name));
                Ok(textual_pass.visit_function(module.data(), function))
            }
        }
    }
}

impl<'c> PipelinePass<'c, MirModule<'c>, MirModule<'c>> for MirEmitPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        if !pipeline.opts.emit_mir {
            return Ok(input);
        }

        let textual_pass = MirModuleTextualPass::default();
        // If no query patterns have been specified, we dump the entire module.
        if pipeline.opts.queries.is_empty() {
            let text =
                MirModuleTextualPass::format_doc_to_string(textual_pass.visit_module(&input));
            eprintln!("{}", text);
            return Ok(input);
        }
        // Otherwise, we emit the results of the queries.
        for query in pipeline.opts.queries.iter() {
            let EmitQuery::Mir(query) = query else {
                continue;
            };
            let target = Self::decode(pipeline, query, &input, &textual_pass)?;
            let text = MirModuleTextualPass::format_doc_to_string(target);
            eprintln!("{}", text);
        }
        Ok(input)
    }
}
