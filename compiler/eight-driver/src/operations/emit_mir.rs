use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use crate::query::{EmitQuery, MirEmitQuery};
use eight_diagnostics::ice;
use eight_middle::mir::module::MirModule;
use eight_mir::textual_pass::{Document, MirModuleTextualPass};

pub struct EmitMirOperation {}

impl EmitMirOperation {
    pub fn decode<'c: 'p, 'p>(
        pipeline: &'c Pipeline<'c>,
        query: &MirEmitQuery,
        module: &'p MirModule<'p>,
        textual_pass: &'p MirModuleTextualPass<'p>,
    ) -> Result<Document<'p>, PipelineError> {
        match query {
            MirEmitQuery::Function(name) => {
                // TODO: This shouldn't really happen...
                let name = pipeline.cc.intern_str(name);
                let function = module
                    .data()
                    .get_function_by_name(name)
                    .unwrap_or_else(|| ice!(format!("function {} not found", name)));
                Ok(textual_pass.visit_function(module.data(), function))
            }
        }
    }
}

impl<'c> PipelineOperation<'c, MirModule<'c>, MirModule<'c>> for EmitMirOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        if !pipeline.opts.emit_mir || pipeline.opts.syntax_only {
            return Ok(input);
        }

        let textual_pass = MirModuleTextualPass::default();
        // If no query patterns have been specified, we dump the entire module.
        if pipeline.opts.queries.is_empty() {
            let text =
                MirModuleTextualPass::format_doc_to_string(textual_pass.visit_module(&input));
            println!("{}", text);
            return Ok(input);
        }
        // Otherwise, we emit the results of the queries.
        for query in pipeline.opts.queries.iter() {
            let EmitQuery::Mir(query) = query else {
                continue;
            };
            let target = Self::decode(pipeline, query, &input, &textual_pass)?;
            let text = MirModuleTextualPass::format_doc_to_string(target);
            println!("{}", text);
        }
        Ok(input)
    }
}
