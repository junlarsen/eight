llvm_map_components_to_libnames(LLVMLibs Support)
add_xd_executable(xdc SOURCES XDCompiler.cpp LIBS ${LLVMLibs} XDDriver)
