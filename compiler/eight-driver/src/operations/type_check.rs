use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_diagnostics::ice;
use eight_middle::hir::HirModule;
use eight_middle::hir_query::HirSignatureQueryDatabase;
use eight_middle::hir_type_check_pass::{HirModuleTypeCheckerPass, TypingContext};

/// Operation for type checking the HIR.
pub struct TypeCheckOperation {}
impl<'c> PipelineOperation<'c, HirModule<'c>, HirModule<'c>> for TypeCheckOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        mut input: HirModule<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let query_database = HirSignatureQueryDatabase::new(input.signature);
        pipeline
            .hir_query_database
            .set(query_database)
            .unwrap_or_else(|_| {
                ice!("failed to assign OnceCell for query database");
            });

        let mut typing_context = TypingContext::new(
            &pipeline.cc,
            pipeline
                .hir_query_database
                .get()
                .unwrap_or_else(|| ice!("failed to get query database")),
        );
        HirModuleTypeCheckerPass::visit(&mut input, &mut typing_context)?;
        Ok(input)
    }
}
