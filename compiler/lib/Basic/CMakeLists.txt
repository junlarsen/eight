add_xd_library(XDBasic SOURCES DiagnosticManager.cpp LIBS)
add_dependencies(XDBasic Diagnostics.td)
