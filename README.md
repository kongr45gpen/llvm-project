# LLVM with Reflection 

A fork of [llvm/llvm-project](https://github.com/llvm/llvm-project) with reflection features added to Clang.

Originally implemented in [matus-chochlik/llvm-project](https://github.com/matus-chochlik/llvm-project). llvm version updated to 17 in [kongr45gpen/llvm-project](https://github.com/kongr45gpen/llvm-project).

## Installation

Follow the original [LLVM building instructions](https://llvm.org/docs/CMake.html).

The following pipeline is suggested for this repository:
```bash
# You can add --depth=1 to make the clone slightly faster
git clone https://github.com/kongr45gpen/llvm-project.git
cd llvm-project
cmake -S llvm -B build -G "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang" -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi" -DLLVM_TARGETS_TO_BUILD=X86
cmake --build build -- -j 8 clang # 8 parallel jobs
```

After running this:
- The `clang++` toolchain should be available in `build/bin`
- The `libcxx` implementation of the standard library will be available in `build/libcxx`

## Compiling

To compile with a reflection-enabled compiler and all modern C++ features, you need to make sure to include the correct compiler file, and standard C++ library.
Make sure to include the proper command line arguments to enable reflection and reflection extensions as well:
```bash
/path/to/llvm-project/build/bin/clang++ -freflection-ts -freflection-ext -stdlib=libc++
```

To link with libcxx dynamically, add it to your LD_LIBRARY_PATH:
```bash
LD_LIBRARY_PATH="/path/to/llvm-project/build/lib/x86_64-linux-gnu"
```

To link with libcxx statically, add the following arguments:
```bash
-static -lc++abi -fuse-ld=lld
```

## Example

See [kongr45gpen/ok-serializer](https://github.com/kongr45gpen/ok-serializer) for an example project of this.
