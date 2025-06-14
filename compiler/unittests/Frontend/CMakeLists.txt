llvm_map_components_to_libnames(LLVMLibs Support)

add_xd_test(FrontendTests SOURCES LexerTest.cpp LoweringTests.cpp ModuleGraphTest.cpp ParserTest.cpp SyntaxTest.cpp LIBS XDFrontend XDDriver ${LLVMLibs})
