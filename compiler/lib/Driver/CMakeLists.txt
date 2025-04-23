llvm_map_components_to_libnames(LLVMLibs Support)
add_xd_library(XDDriver SOURCES CompilerInstance.cpp Workspace.cpp LIBS ${LLVMLibs} XDBasic XDFrontend)
