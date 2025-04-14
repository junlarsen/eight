# Stage 1: Build TableGen
add_subdirectory(lib/TableGen)
add_subdirectory(tools/xd-tablegen)

# Stage 2: Compile all TableGen files
add_subdirectory(include/xd/Basic)

# Stage 3: Build everything else that may depend on TableGen
add_subdirectory(lib/Basic)
add_subdirectory(lib/Frontend)
add_subdirectory(tools/xd-driver)
add_subdirectory(unittests/Frontend)
