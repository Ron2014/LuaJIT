set(DASMDIR ../dynasm)
set(DASM "${DASMDIR}/dynasm.lua")

if(FIPS_WIN64)
set(DASC vm_x64.dasc)
set(DASMFLAGS -D WIN -D JIT -D FFI -D P64)
endif()

if(FIPS_WIN32)
set(DASC vm_x86.dasc)
set(DASMFLAGS -D WIN -D JIT -D FFI)
endif()

set(ALL_LIB lib_base.c lib_math.c lib_bit.c lib_string.c lib_table.c lib_io.c lib_os.c lib_package.c lib_debug.c lib_jit.c lib_ffi.c)

if(FIPS_WINDOWS)
add_definitions(-D_CRT_SECURE_NO_DEPRECATE)
add_definitions("-D_CRT_STDIO_INLINE=__declspec(dllexport) inline")
set(COMMAND_RUN start /B)
set(BUILDVM ${FIPS_PROJECT_DEPLOY_DIR}/buildvm.exe)
else()
set(COMMAND_RUN bash)
set(BUILDVM ${FIPS_PROJECT_DEPLOY_DIR}/buildvm)
endif()


fips_begin_app(minilua cmdline)
fips_vs_disable_warnings(4819)
fips_files(host/minilua.c)
if(FIPS_POSIX)
    fips_libs(m)
endif()
fips_end_app()

add_custom_target(Gen_buildvm_arch)
add_custom_command(TARGET Gen_buildvm_arch
    POST_BUILD
    COMMAND cd ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND ${COMMAND_RUN} ${FIPS_PROJECT_DEPLOY_DIR}/minilua ${DASM} -LN ${DASMFLAGS} -o host/buildvm_arch.h ${DASC}
    DEPENDS minilua
)

fips_begin_app(buildvm cmdline)
fips_vs_disable_warnings(4819)
fips_include_directories(.)
fips_include_directories(${DASMDIR})
fips_files_ex(host buildvm*.c GROUP "sources")
fips_end_app()

add_custom_target(Gen_buildvm)
add_custom_command(TARGET Gen_buildvm
    POST_BUILD
    COMMAND cd ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m peobj -o lj_vm.obj  
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m bcdef -o lj_bcdef.h ${ALL_LIB}  
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m ffdef -o lj_ffdef.h ${ALL_LIB}  
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m libdef -o lj_libdef.h ${ALL_LIB}    
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m recdef -o lj_recdef.h ${ALL_LIB}    
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m vmdef -o jit/vmdef.lua ${ALL_LIB}   
    COMMAND ${COMMAND_RUN} ${BUILDVM} -m folddef -o lj_folddef.h lj_opt_fold.c
    DEPENDS buildvm
)

fips_begin_lib(luajit_liblua51)
fips_vs_disable_warnings(4819 4700)
fips_files_ex(. lj_*.c lib_*.c lj_vm.obj GROUP "sources")
fips_end_lib()

add_dependencies(luajit_liblua51 Gen_buildvm)

fips_begin_sharedlib(luajit_dlllua51)
fips_vs_disable_warnings(4819 4700)
fips_files_ex(. lj_*.c lib_*.c lj_vm.obj GROUP "sources")
fips_end_sharedlib()

add_dependencies(luajit_dlllua51 Gen_buildvm)

fips_begin_app(luajit cmdline)
fips_files(luajit.c)
fips_deps(luajit_liblua51)
fips_end_app()