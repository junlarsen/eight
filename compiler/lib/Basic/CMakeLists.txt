llvm_map_components_to_libnames(LLVMLibs Support)
add_xd_library(XDBasic SOURCES DiagnosticManager.cpp SourceManager.cpp LIBS ${LLVMLibs})
add_dependencies(XDBasic Diagnostics.td)
