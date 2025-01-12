use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_diagnostics::ice;
use eight_hir::query::HirSignatureQueryDatabase;
use eight_hir::type_check_pass::{HirModuleTypeCheckerPass, TypingContext};
use eight_hir::HirModule;

/// Operation for type checking the HIR.
pub struct TypeCheckOperation {}
impl<'hir> PipelineOperation<'hir, HirModule<'hir>, HirModule<'hir>> for TypeCheckOperation {
    fn execute(
        pipeline: &'hir Pipeline<'hir>,
        mut input: HirModule<'hir>,
    ) -> Result<HirModule<'hir>, PipelineError> {
        let query_database = HirSignatureQueryDatabase::new(input.signature);
        pipeline
            .hir_query_database
            .set(query_database)
            .unwrap_or_else(|_| {
                ice!("failed to assign OnceCell for query database");
            });

        let mut typing_context = TypingContext::new(
            &pipeline.hir_arena,
            pipeline
                .hir_query_database
                .get()
                .unwrap_or_else(|| ice!("failed to get query database")),
        );
        HirModuleTypeCheckerPass::visit(&mut input, &mut typing_context)?;
        Ok(input)
    }
}
