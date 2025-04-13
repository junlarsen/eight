llvm_map_components_to_libnames(LLVMLibs Support TableGen)
add_xd_library(XDTableGen SOURCES DiagnosticEmitter.cpp LIBS ${LLVMLibs})
