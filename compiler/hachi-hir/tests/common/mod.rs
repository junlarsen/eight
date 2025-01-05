/// A macro for building a HIR module from source code, and asserting that the syntax tree for the
/// module can be lowered into HIR.
#[macro_export]
macro_rules! assert_hir_module_compiles {
    ($input:expr) => {{
        use bumpalo::Bump;
        use hachi_hir::passes::ASTSyntaxLoweringPass;
        use hachi_hir::ty::HirTyArena;
        use hachi_syntax::Lexer;
        use hachi_syntax::Parser;

        let mut lexer = Lexer::new($input);
        let mut parser = Parser::new(&mut lexer);
        let translation_unit = parser
            .parse()
            .expect("failed to parse corpus file into syntax tree");

        let bump = Bump::new();
        let arena = HirTyArena::new(&bump);

        let mut lowering_pass = ASTSyntaxLoweringPass::new(&arena);
        let module = lowering_pass
            .visit_translation_unit(&translation_unit)
            .expect("failed to lower translation unit");
        let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
        insta::assert_snapshot!(doc);
    }};
}

#[macro_export]
macro_rules! assert_hir_module_infers {
    ($input:expr) => {{
        use bumpalo::Bump;
        use hachi_hir::passes::ASTSyntaxLoweringPass;
        use hachi_hir::passes::HirModuleTypeCheckerPass;
        use hachi_hir::passes::TypingContext;
        use hachi_hir::ty::HirTyArena;
        use hachi_syntax::Lexer;
        use hachi_syntax::Parser;

        let mut lexer = Lexer::new($input);
        let mut parser = Parser::new(&mut lexer);
        let translation_unit = parser
            .parse()
            .expect("failed to parse corpus file into syntax tree");

        let bump = Bump::new();
        let arena = HirTyArena::new(&bump);

        let mut lowering_pass = ASTSyntaxLoweringPass::new(&arena);
        let mut module = lowering_pass
            .visit_translation_unit(&translation_unit)
            .expect("failed to lower translation unit");

        let mut cx = TypingContext::new(&arena);
        HirModuleTypeCheckerPass::visit(&mut module, &mut cx)
            .expect("failed to type check corpus file");

        let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
        insta::assert_snapshot!(doc);
    }};
}
