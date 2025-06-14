llvm_map_components_to_libnames(LLVMLibs Support)
add_xd_library(XDDriver SOURCES CompilerInstance.cpp Package.cpp LIBS ${LLVMLibs} XDBasic XDFrontend)
