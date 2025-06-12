# Run clang-format on all files in the project
fmt:
    #!/bin/sh
    fd '*{h,cpp,td,inc}' --glob | xargs clang-format -i
