/// A macro for building a HIR module from source code, and asserting that the syntax tree for the
/// module can be lowered into HIR.
#[macro_export]
macro_rules! assert_hir_module_compiles {
    ($input:expr, $path:expr) => {{
        use bumpalo::Bump;
        use eight_hir::arena::HirArena;
        use eight_hir::passes::ASTSyntaxLoweringPass;
        use eight_syntax::lexer::Lexer;
        use eight_syntax::parser::Parser;
        use eight_syntax::arena::AstArena;

        let mut lexer = Lexer::new($input);
        let bump = Bump::new();
        let arena = AstArena::new(&bump);
        let mut parser = Parser::new(&mut lexer, &arena);
        let translation_unit = parser
            .parse()
            .expect(format!("failed to parse {} into syntax tree", $path.display()).as_str());

        let bump = Bump::new();
        let arena = HirArena::new(&bump);

        let lowering_pass = ASTSyntaxLoweringPass::new(&arena);
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
        use eight_hir::arena::HirArena;
        use eight_hir::passes::ASTSyntaxLoweringPass;
        use eight_hir::passes::HirModuleTypeCheckerPass;
        use eight_hir::passes::TypingContext;
        use eight_syntax::lexer::Lexer;
        use eight_syntax::parser::Parser;
        use eight_syntax::arena::AstArena;

        let bump = Bump::new();
        let arena = AstArena::new(&bump);
        let mut lexer = Lexer::new($input);
        let mut parser = Parser::new(&mut lexer, &arena);
        let translation_unit = parser
            .parse()
            .expect("failed to parse corpus file into syntax tree");

        let bump = Bump::new();
        let arena = HirArena::new(&bump);

        let lowering_pass = ASTSyntaxLoweringPass::new(&arena);
        let mut module = lowering_pass
            .visit_translation_unit(&translation_unit)
            .expect("failed to lower translation unit");

        let mut cx = TypingContext::new(&arena, module.signature);
        HirModuleTypeCheckerPass::visit(&mut module, &mut cx)
            .expect("failed to type check corpus file");

        let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
        insta::assert_snapshot!(doc);
    }};
}
