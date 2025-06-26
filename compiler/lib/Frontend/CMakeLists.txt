llvm_map_components_to_libnames(LLVMLibs Support)

add_xd_library(XDFrontend SOURCES AST.cpp Lexer.cpp Parser.cpp Syntax.cpp LIBS XDBasic ${LLVMLibs})
