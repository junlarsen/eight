use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_mir::textual_pass::MirModuleTextualPass;
use eight_mir::MirModule;

pub struct EmitMirOperation {}

impl<'c> PipelineOperation<'c, MirModule<'c>, MirModule<'c>> for EmitMirOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        if !pipeline.opts.emit_mir {
            return Ok(input);
        }

        let textual_pass = MirModuleTextualPass::default();
        let doc = textual_pass.visit_module(&input);
        let text = MirModuleTextualPass::format_doc_to_string(doc);
        println!("{}", text);

        Ok(input)
    }
}
