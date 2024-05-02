// Lean compiler output
// Module: Lake.Build.Common
// Imports: Init Lake.Config.Monad Lake.Build.Actions
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* l_Lake_MTime_instOrd;
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100_(lean_object*);
static lean_object* l_Lake_replayBuildLog___closed__2;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lake_fetchFileTrace___closed__1;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_replayBuildLog___closed__3;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
LEAN_EXPORT uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_BuildJob_collectList___rarg(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_replayBuildLog___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__1___closed__2;
LEAN_EXPORT uint64_t l_Lake_platformTrace;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheBuildLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object*);
static lean_object* l_Lake_buildO___lambda__1___closed__1;
static lean_object* l_Lake_computeDynlibOfShared___lambda__1___closed__4;
static lean_object* l_Lake_replayBuildLog___closed__5;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate(lean_object*);
lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildLeanO___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4;
lean_object* l_Lake_BuildJob_collectArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
static uint8_t l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_replayBuildLog___closed__4;
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___closed__1;
lean_object* l_System_FilePath_fileStem(lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lake_replayBuildLog(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_computeDynlibOfShared___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*);
lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___at_Lake_buildO___spec__1___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_replayBuildLog___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lambda__3___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheBuildLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildStaticLib___lambda__2___closed__1;
static lean_object* l_Lake_buildFileUnlessUpToDate___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_inputFile___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static uint64_t _init_l_Lake_platformTrace___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_System_Platform_target;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 1723;
x_2 = l_Lake_platformTrace___closed__1;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lake_platformTrace() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_platformTrace___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_Hash_load_x3f(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_2(x_2, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lake_MTime_instOrd;
x_19 = l_instDecidableRelLt___rarg(x_18, x_17, x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lake_MTime_instOrd;
x_26 = l_instDecidableRelLt___rarg(x_25, x_24, x_22);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_11, 1);
x_42 = lean_ctor_get(x_11, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_46 = lean_unbox_uint64(x_44);
lean_dec(x_44);
x_47 = lean_uint64_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
lean_ctor_set(x_11, 0, x_49);
return x_11;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_free_object(x_11);
x_50 = lean_apply_2(x_1, x_3, x_41);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_7);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_dec(x_11);
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_ctor_get(x_4, 0);
lean_inc(x_60);
lean_dec(x_4);
x_61 = lean_unbox_uint64(x_59);
lean_dec(x_59);
x_62 = lean_unbox_uint64(x_60);
lean_dec(x_60);
x_63 = lean_uint64_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_apply_2(x_1, x_3, x_58);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_7);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_1);
x_73 = lean_apply_2(x_2, x_3, x_8);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_4, 1);
lean_inc(x_76);
lean_dec(x_4);
x_77 = l_Lake_MTime_instOrd;
x_78 = l_instDecidableRelLt___rarg(x_77, x_76, x_75);
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_7);
lean_ctor_set(x_73, 0, x_80);
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
lean_dec(x_4);
x_84 = l_Lake_MTime_instOrd;
x_85 = l_instDecidableRelLt___rarg(x_84, x_83, x_81);
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_73);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_73, 0);
lean_dec(x_90);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_7);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_93);
return x_73;
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_73, 1);
lean_inc(x_94);
lean_dec(x_73);
x_95 = 0;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_7);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildTrace_checkUpToDate___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildTrace_checkUpToDate___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
static uint8_t _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_4);
x_10 = l_Lake_BuildTrace_checkUpToDate___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, 2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_apply_3(x_6, x_7, x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_39; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
lean_inc(x_5);
x_39 = l_System_FilePath_parent(x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_unbox_uint64(x_40);
lean_dec(x_40);
x_42 = lean_uint64_to_nat(x_41);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
x_44 = l_IO_FS_writeFile(x_5, x_43, x_20);
lean_dec(x_43);
lean_dec(x_5);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_24 = x_47;
x_25 = x_46;
goto block_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_24 = x_50;
x_25 = x_49;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = l_IO_FS_createDirAll(x_51, x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
lean_dec(x_4);
x_55 = lean_unbox_uint64(x_54);
lean_dec(x_54);
x_56 = lean_uint64_to_nat(x_55);
x_57 = l___private_Init_Data_Repr_0__Nat_reprFast(x_56);
x_58 = l_IO_FS_writeFile(x_5, x_57, x_53);
lean_dec(x_57);
lean_dec(x_5);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_24 = x_61;
x_25 = x_60;
goto block_38;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_24 = x_64;
x_25 = x_63;
goto block_38;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_5);
lean_dec(x_4);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_dec(x_52);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_24 = x_67;
x_25 = x_66;
goto block_38;
}
}
block_38:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_io_error_to_string(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_22);
x_31 = lean_array_push(x_22, x_29);
if (lean_is_scalar(x_23)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_23;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_21)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_21;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_34 = 0;
x_35 = lean_box(x_34);
if (lean_is_scalar(x_23)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_23;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
if (lean_is_scalar(x_21)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_21;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
return x_37;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_5);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_18, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
return x_18;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_19, 0);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_19);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_18, 0, x_73);
return x_18;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_dec(x_18);
x_75 = lean_ctor_get(x_19, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_77 = x_19;
} else {
 lean_dec_ref(x_19);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_18);
if (x_80 == 0)
{
return x_18;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_18, 0);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_18);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_84 = lean_ctor_get(x_10, 1);
lean_inc(x_84);
lean_dec(x_10);
x_85 = !lean_is_exclusive(x_11);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_11, 1);
x_87 = lean_ctor_get(x_11, 0);
lean_dec(x_87);
x_88 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_89 = lean_io_exit(x_88, x_84);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_ctor_set(x_11, 0, x_91);
lean_ctor_set(x_89, 0, x_11);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_89);
lean_ctor_set(x_11, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_89);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_io_error_to_string(x_96);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_86);
x_101 = lean_array_push(x_86, x_99);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_101);
lean_ctor_set(x_11, 0, x_100);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 0, x_11);
return x_89;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_104 = lean_io_error_to_string(x_102);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_array_get_size(x_86);
x_108 = lean_array_push(x_86, x_106);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_108);
lean_ctor_set(x_11, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_11);
lean_ctor_set(x_109, 1, x_103);
return x_109;
}
}
}
else
{
lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_dec(x_11);
x_111 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_112 = lean_io_exit(x_111, x_84);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_110);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
x_121 = lean_io_error_to_string(x_118);
x_122 = 3;
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
x_124 = lean_array_get_size(x_110);
x_125 = lean_array_push(x_110, x_123);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_120)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_120;
 lean_ctor_set_tag(x_127, 0);
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_119);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_10);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_10, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_11);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_11, 0);
lean_dec(x_131);
x_132 = 1;
x_133 = lean_box(x_132);
lean_ctor_set(x_11, 0, x_133);
return x_10;
}
else
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
lean_dec(x_11);
x_135 = 1;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_10, 0, x_137);
return x_10;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_10, 1);
lean_inc(x_138);
lean_dec(x_10);
x_139 = lean_ctor_get(x_11, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_140 = x_11;
} else {
 lean_dec_ref(x_11);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = lean_box(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_4);
x_27 = l_Lake_BuildTrace_checkUpToDate___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_31, 2);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_apply_3(x_6, x_7, x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_53; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_5);
x_53 = l_System_FilePath_parent(x_5);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
lean_dec(x_4);
x_55 = lean_unbox_uint64(x_54);
lean_dec(x_54);
x_56 = lean_uint64_to_nat(x_55);
x_57 = l___private_Init_Data_Repr_0__Nat_reprFast(x_56);
x_58 = l_IO_FS_writeFile(x_5, x_57, x_37);
lean_dec(x_57);
lean_dec(x_5);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_40 = x_61;
x_41 = x_60;
goto block_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_40 = x_64;
x_41 = x_63;
goto block_52;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_66 = l_IO_FS_createDirAll(x_65, x_37);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_4, 0);
lean_inc(x_68);
lean_dec(x_4);
x_69 = lean_unbox_uint64(x_68);
lean_dec(x_68);
x_70 = lean_uint64_to_nat(x_69);
x_71 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_72 = l_IO_FS_writeFile(x_5, x_71, x_67);
lean_dec(x_71);
lean_dec(x_5);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_40 = x_75;
x_41 = x_74;
goto block_52;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_40 = x_78;
x_41 = x_77;
goto block_52;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_5);
lean_dec(x_4);
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_dec(x_66);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_79);
x_40 = x_81;
x_41 = x_80;
goto block_52;
}
}
block_52:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_io_error_to_string(x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_38);
x_47 = lean_array_push(x_38, x_45);
if (lean_is_scalar(x_39)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_39;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_10 = x_48;
x_11 = x_41;
goto block_26;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_49 = 0;
x_50 = lean_box(x_49);
if (lean_is_scalar(x_39)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_39;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
x_10 = x_51;
x_11 = x_41;
goto block_26;
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_dec(x_35);
x_83 = !lean_is_exclusive(x_36);
if (x_83 == 0)
{
x_10 = x_36;
x_11 = x_82;
goto block_26;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_36, 0);
x_85 = lean_ctor_get(x_36, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_36);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_10 = x_86;
x_11 = x_82;
goto block_26;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_35);
if (x_87 == 0)
{
return x_35;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_35, 0);
x_89 = lean_ctor_get(x_35, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_35);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = lean_ctor_get(x_27, 1);
lean_inc(x_91);
lean_dec(x_27);
x_92 = !lean_is_exclusive(x_28);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_28, 1);
x_94 = lean_ctor_get(x_28, 0);
lean_dec(x_94);
x_95 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_96 = lean_io_exit(x_95, x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_ctor_set(x_28, 0, x_97);
x_10 = x_28;
x_11 = x_98;
goto block_26;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_io_error_to_string(x_99);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_array_get_size(x_93);
x_105 = lean_array_push(x_93, x_103);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_105);
lean_ctor_set(x_28, 0, x_104);
x_10 = x_28;
x_11 = x_100;
goto block_26;
}
}
else
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_28, 1);
lean_inc(x_106);
lean_dec(x_28);
x_107 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_108 = lean_io_exit(x_107, x_91);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_106);
x_10 = x_111;
x_11 = x_110;
goto block_26;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_io_error_to_string(x_112);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_106);
x_118 = lean_array_push(x_106, x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_10 = x_119;
x_11 = x_113;
goto block_26;
}
}
}
}
else
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_ctor_get(x_27, 1);
lean_inc(x_120);
lean_dec(x_27);
x_121 = !lean_is_exclusive(x_28);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_28, 0);
lean_dec(x_122);
x_123 = 1;
x_124 = lean_box(x_123);
lean_ctor_set(x_28, 0, x_124);
x_10 = x_28;
x_11 = x_120;
goto block_26;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_28, 1);
lean_inc(x_125);
lean_dec(x_28);
x_126 = 1;
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_10 = x_128;
x_11 = x_120;
goto block_26;
}
}
block_26:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeFileHash(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_metadata(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lake_fetchFileTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".hash", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_5, 1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1(x_1, x_4);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_io_error_to_string(x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_3);
x_21 = lean_array_push(x_3, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_3);
x_29 = lean_array_push(x_3, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_126; lean_object* x_127; 
x_32 = l_Lake_fetchFileTrace___closed__1;
lean_inc(x_1);
x_33 = lean_string_append(x_1, x_32);
x_126 = l_Lake_Hash_load_x3f(x_33, x_4);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lake_computeFileHash(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_3);
x_34 = x_132;
x_35 = x_131;
goto block_125;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_io_error_to_string(x_133);
x_136 = 3;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
x_138 = lean_array_get_size(x_3);
x_139 = lean_array_push(x_3, x_137);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_34 = x_140;
x_35 = x_134;
goto block_125;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_33);
x_141 = lean_ctor_get(x_126, 1);
lean_inc(x_141);
lean_dec(x_126);
x_142 = lean_ctor_get(x_127, 0);
lean_inc(x_142);
lean_dec(x_127);
x_143 = lean_io_metadata(x_1, x_141);
lean_dec(x_1);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_3);
lean_ctor_set(x_143, 0, x_148);
return x_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_143, 0);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_143);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_142);
x_155 = !lean_is_exclusive(x_143);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_143, 0);
x_157 = lean_io_error_to_string(x_156);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_get_size(x_3);
x_161 = lean_array_push(x_3, x_159);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_tag(x_143, 0);
lean_ctor_set(x_143, 0, x_162);
return x_143;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_163 = lean_ctor_get(x_143, 0);
x_164 = lean_ctor_get(x_143, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_143);
x_165 = lean_io_error_to_string(x_163);
x_166 = 3;
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_166);
x_168 = lean_array_get_size(x_3);
x_169 = lean_array_push(x_3, x_167);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_164);
return x_171;
}
}
}
block_125:
{
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_unbox_uint64(x_37);
x_40 = lean_uint64_to_nat(x_39);
x_41 = l___private_Init_Data_Repr_0__Nat_reprFast(x_40);
x_42 = l_IO_FS_writeFile(x_33, x_41, x_35);
lean_dec(x_41);
lean_dec(x_33);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_io_metadata(x_1, x_43);
lean_dec(x_1);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_34, 0, x_48);
lean_ctor_set(x_44, 0, x_34);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_34, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_37);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_io_error_to_string(x_55);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_38);
x_60 = lean_array_push(x_38, x_58);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_60);
lean_ctor_set(x_34, 0, x_59);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_34);
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_io_error_to_string(x_61);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_38);
x_67 = lean_array_push(x_38, x_65);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_67);
lean_ctor_set(x_34, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_34);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_42, 0);
x_71 = lean_io_error_to_string(x_70);
x_72 = 3;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_get_size(x_38);
x_75 = lean_array_push(x_38, x_73);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_75);
lean_ctor_set(x_34, 0, x_74);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_34);
return x_42;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_42, 0);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_42);
x_78 = lean_io_error_to_string(x_76);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_38);
x_82 = lean_array_push(x_38, x_80);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_82);
lean_ctor_set(x_34, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_34);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_34, 0);
x_85 = lean_ctor_get(x_34, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_34);
x_86 = lean_unbox_uint64(x_84);
x_87 = lean_uint64_to_nat(x_86);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_87);
x_89 = l_IO_FS_writeFile(x_33, x_88, x_35);
lean_dec(x_88);
lean_dec(x_33);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_io_metadata(x_1, x_90);
lean_dec(x_1);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_85);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_84);
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_101 = x_91;
} else {
 lean_dec_ref(x_91);
 x_101 = lean_box(0);
}
x_102 = lean_io_error_to_string(x_99);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_get_size(x_85);
x_106 = lean_array_push(x_85, x_104);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_101;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_84);
lean_dec(x_1);
x_109 = lean_ctor_get(x_89, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_89, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_111 = x_89;
} else {
 lean_dec_ref(x_89);
 x_111 = lean_box(0);
}
x_112 = lean_io_error_to_string(x_109);
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_array_get_size(x_85);
x_116 = lean_array_push(x_85, x_114);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_111;
 lean_ctor_set_tag(x_118, 0);
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_33);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_34);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_34);
lean_ctor_set(x_120, 1, x_35);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_34, 0);
x_122 = lean_ctor_get(x_34, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_34);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_35);
return x_124;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_fetchFileTrace(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeFileHash(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_fetchFileTrace___closed__1;
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_to_nat(x_8);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_9);
x_11 = l_IO_FS_writeFile(x_7, x_10, x_5);
lean_dec(x_10);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100_(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_replayBuildLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cached build log is corrupted: ", 31);
return x_1;
}
}
static lean_object* _init_l_Lake_replayBuildLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_replayBuildLog___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to read cached build log: ", 33);
return x_1;
}
}
static lean_object* _init_l_Lake_replayBuildLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected JSON array, got '", 26);
return x_1;
}
}
static lean_object* _init_l_Lake_replayBuildLog___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_replayBuildLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_67; 
x_67 = l_IO_FS_readFile(x_1, x_3);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_2);
x_4 = x_71;
x_5 = x_69;
goto block_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_2);
x_4 = x_75;
x_5 = x_73;
goto block_66;
}
block_66:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_8 = x_4;
} else {
 lean_dec_ref(x_4);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 11)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_io_error_to_string(x_21);
x_26 = l_Lake_replayBuildLog___closed__3;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_replayBuildLog___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = 2;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_7, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lean_Json_parse(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_9 = x_38;
goto block_20;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 4)
{
lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = 0;
x_44 = l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1(x_42, x_43, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_9 = x_45;
goto block_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_8);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_47, x_47);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
lean_dec(x_46);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
else
{
size_t x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_58 = lean_box(0);
x_59 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_46, x_43, x_57, x_58, x_7, x_5);
lean_dec(x_46);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_unsigned_to_nat(80u);
x_61 = l_Lean_Json_pretty(x_39, x_60);
x_62 = l_Lake_replayBuildLog___closed__4;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l_Lake_replayBuildLog___closed__5;
x_65 = lean_string_append(x_63, x_64);
x_9 = x_65;
goto block_20;
}
}
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lake_replayBuildLog___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_replayBuildLog___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = 2;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_push(x_7, x_15);
x_17 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_8;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_replayBuildLog___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_replayBuildLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_replayBuildLog(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054_(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheBuildLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_apply_3(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_13);
x_16 = l_Array_extract___rarg(x_13, x_6, x_15);
x_17 = l_Array_isEmpty___rarg(x_16);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_7);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(x_19, x_20, x_16);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_22, x_23);
x_25 = l_IO_FS_writeFile(x_1, x_24, x_10);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_8, 0, x_27);
lean_ctor_set(x_25, 0, x_8);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_8, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_io_error_to_string(x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_13, x_35);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_36);
lean_ctor_set(x_8, 0, x_15);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_8);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_io_error_to_string(x_37);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_push(x_13, x_41);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_42);
lean_ctor_set(x_8, 0, x_15);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_15);
x_44 = lean_box(0);
lean_ctor_set(x_8, 0, x_44);
return x_7;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = lean_array_get_size(x_45);
x_47 = l_Array_extract___rarg(x_45, x_6, x_46);
x_48 = l_Array_isEmpty___rarg(x_47);
if (x_48 == 0)
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_7);
x_49 = lean_array_get_size(x_47);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = 0;
x_52 = l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(x_50, x_51, x_47);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(80u);
x_55 = l_Lean_Json_pretty(x_53, x_54);
x_56 = l_IO_FS_writeFile(x_1, x_55, x_10);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_45);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
x_65 = lean_io_error_to_string(x_62);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_45, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_46);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
 lean_ctor_set_tag(x_70, 0);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_47);
lean_dec(x_46);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_45);
lean_ctor_set(x_7, 0, x_72);
return x_7;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
lean_dec(x_7);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_75 = x_8;
} else {
 lean_dec_ref(x_8);
 x_75 = lean_box(0);
}
x_76 = lean_array_get_size(x_74);
x_77 = l_Array_extract___rarg(x_74, x_6, x_76);
x_78 = l_Array_isEmpty___rarg(x_77);
if (x_78 == 0)
{
lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_array_get_size(x_77);
x_80 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_81 = 0;
x_82 = l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(x_80, x_81, x_77);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_unsigned_to_nat(80u);
x_85 = l_Lean_Json_pretty(x_83, x_84);
x_86 = l_IO_FS_writeFile(x_1, x_85, x_73);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_75;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_74);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_94 = x_86;
} else {
 lean_dec_ref(x_86);
 x_94 = lean_box(0);
}
x_95 = lean_io_error_to_string(x_92);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_push(x_74, x_97);
if (lean_is_scalar(x_75)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_75;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_76);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
 lean_ctor_set_tag(x_100, 0);
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_93);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_77);
lean_dec(x_76);
x_101 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_75;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_74);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_73);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_6);
x_104 = !lean_is_exclusive(x_7);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_7, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_8);
if (x_106 == 0)
{
return x_7;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_8, 0);
x_108 = lean_ctor_get(x_8, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_8);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_7, 0, x_109);
return x_7;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_7, 1);
lean_inc(x_110);
lean_dec(x_7);
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_113 = x_8;
} else {
 lean_dec_ref(x_8);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_6);
x_116 = !lean_is_exclusive(x_7);
if (x_116 == 0)
{
return x_7;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_7, 0);
x_118 = lean_ctor_get(x_7, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_7);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_cacheBuildLog___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheBuildLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_cacheBuildLog(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get_uint8(x_7, 0);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lake_Hash_load_x3f(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_io_metadata(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lake_MTime_instOrd;
x_18 = l_instDecidableRelLt___rarg(x_17, x_16, x_15);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Lake_MTime_instOrd;
x_26 = l_instDecidableRelLt___rarg(x_25, x_24, x_23);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_12, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_9, 1);
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_46 = lean_unbox_uint64(x_44);
lean_dec(x_44);
x_47 = lean_uint64_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
lean_ctor_set(x_9, 0, x_49);
return x_9;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_free_object(x_9);
x_50 = l_System_FilePath_pathExists(x_1, x_41);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_5);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_dec(x_9);
x_59 = lean_ctor_get(x_10, 0);
lean_inc(x_59);
lean_dec(x_10);
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_unbox_uint64(x_59);
lean_dec(x_59);
x_62 = lean_unbox_uint64(x_60);
lean_dec(x_60);
x_63 = lean_uint64_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = l_System_FilePath_pathExists(x_1, x_58);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_5);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
x_73 = lean_io_metadata(x_1, x_6);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = l_Lake_MTime_instOrd;
x_79 = l_instDecidableRelLt___rarg(x_78, x_77, x_76);
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
lean_ctor_set(x_73, 0, x_81);
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l_Lake_MTime_instOrd;
x_87 = l_instDecidableRelLt___rarg(x_86, x_85, x_84);
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_73);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_73, 0);
lean_dec(x_92);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_95);
return x_73;
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_73, 1);
lean_inc(x_96);
lean_dec(x_73);
x_97 = 0;
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_5);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
}
}
static lean_object* _init_l_Lake_buildFileUnlessUpToDate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".trace", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_buildFileUnlessUpToDate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".log.json", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_7 = l_Lake_buildFileUnlessUpToDate___closed__1;
lean_inc(x_1);
x_8 = lean_string_append(x_1, x_7);
x_9 = l_Lake_buildFileUnlessUpToDate___closed__2;
lean_inc(x_1);
x_10 = lean_string_append(x_1, x_9);
lean_inc(x_2);
x_106 = l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(x_1, x_2, x_8, x_4, x_5, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_4, 0);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_110, 2);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
lean_inc(x_4);
x_114 = l_Lake_cacheBuildLog(x_10, x_3, x_4, x_113, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_132; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
lean_inc(x_8);
x_132 = l_System_FilePath_parent(x_8);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint64_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
lean_dec(x_2);
x_134 = lean_unbox_uint64(x_133);
lean_dec(x_133);
x_135 = lean_uint64_to_nat(x_134);
x_136 = l___private_Init_Data_Repr_0__Nat_reprFast(x_135);
x_137 = l_IO_FS_writeFile(x_8, x_136, x_116);
lean_dec(x_136);
lean_dec(x_8);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
x_119 = x_140;
x_120 = x_139;
goto block_131;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
lean_dec(x_137);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_141);
x_119 = x_143;
x_120 = x_142;
goto block_131;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_132, 0);
lean_inc(x_144);
lean_dec(x_132);
x_145 = l_IO_FS_createDirAll(x_144, x_116);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint64_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
lean_dec(x_2);
x_148 = lean_unbox_uint64(x_147);
lean_dec(x_147);
x_149 = lean_uint64_to_nat(x_148);
x_150 = l___private_Init_Data_Repr_0__Nat_reprFast(x_149);
x_151 = l_IO_FS_writeFile(x_8, x_150, x_146);
lean_dec(x_150);
lean_dec(x_8);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_152);
x_119 = x_154;
x_120 = x_153;
goto block_131;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_155);
x_119 = x_157;
x_120 = x_156;
goto block_131;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_2);
x_158 = lean_ctor_get(x_145, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_145, 1);
lean_inc(x_159);
lean_dec(x_145);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_158);
x_119 = x_160;
x_120 = x_159;
goto block_131;
}
}
block_131:
{
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_io_error_to_string(x_121);
x_123 = 3;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_get_size(x_117);
x_126 = lean_array_push(x_117, x_124);
if (lean_is_scalar(x_118)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_118;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_11 = x_127;
x_12 = x_120;
goto block_105;
}
else
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_119);
x_128 = 0;
x_129 = lean_box(x_128);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_118;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_117);
x_11 = x_130;
x_12 = x_120;
goto block_105;
}
}
}
else
{
lean_object* x_161; uint8_t x_162; 
lean_dec(x_8);
lean_dec(x_2);
x_161 = lean_ctor_get(x_114, 1);
lean_inc(x_161);
lean_dec(x_114);
x_162 = !lean_is_exclusive(x_115);
if (x_162 == 0)
{
x_11 = x_115;
x_12 = x_161;
goto block_105;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_115, 0);
x_164 = lean_ctor_get(x_115, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_115);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_11 = x_165;
x_12 = x_161;
goto block_105;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_114);
if (x_166 == 0)
{
return x_114;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_114, 0);
x_168 = lean_ctor_get(x_114, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_114);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; uint8_t x_171; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_170 = lean_ctor_get(x_106, 1);
lean_inc(x_170);
lean_dec(x_106);
x_171 = !lean_is_exclusive(x_107);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_107, 1);
x_173 = lean_ctor_get(x_107, 0);
lean_dec(x_173);
x_174 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_175 = lean_io_exit(x_174, x_170);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_ctor_set(x_107, 0, x_176);
x_11 = x_107;
x_12 = x_177;
goto block_105;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_io_error_to_string(x_178);
x_181 = 3;
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_181);
x_183 = lean_array_get_size(x_172);
x_184 = lean_array_push(x_172, x_182);
lean_ctor_set_tag(x_107, 1);
lean_ctor_set(x_107, 1, x_184);
lean_ctor_set(x_107, 0, x_183);
x_11 = x_107;
x_12 = x_179;
goto block_105;
}
}
else
{
lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_107, 1);
lean_inc(x_185);
lean_dec(x_107);
x_186 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_187 = lean_io_exit(x_186, x_170);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_185);
x_11 = x_190;
x_12 = x_189;
goto block_105;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_io_error_to_string(x_191);
x_194 = 3;
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = lean_array_get_size(x_185);
x_197 = lean_array_push(x_185, x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_11 = x_198;
x_12 = x_192;
goto block_105;
}
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_106, 1);
lean_inc(x_199);
lean_dec(x_106);
x_200 = !lean_is_exclusive(x_107);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_107, 0);
lean_dec(x_201);
x_202 = 1;
x_203 = lean_box(x_202);
lean_ctor_set(x_107, 0, x_203);
x_11 = x_107;
x_12 = x_199;
goto block_105;
}
else
{
lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_107, 1);
lean_inc(x_204);
lean_dec(x_107);
x_205 = 1;
x_206 = lean_box(x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
x_11 = x_207;
x_12 = x_199;
goto block_105;
}
}
block_105:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
lean_inc(x_1);
x_18 = l_Lake_cacheFileHash(x_1, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_metadata(x_1, x_20);
lean_dec(x_1);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_11, 0, x_25);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_io_error_to_string(x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_16);
x_37 = lean_array_push(x_16, x_35);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_36);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_16);
x_44 = lean_array_push(x_16, x_42);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_44);
lean_ctor_set(x_11, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_io_error_to_string(x_47);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_16);
x_52 = lean_array_push(x_16, x_50);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_52);
lean_ctor_set(x_11, 0, x_51);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_io_error_to_string(x_53);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_16);
x_59 = lean_array_push(x_16, x_57);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_59);
lean_ctor_set(x_11, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
lean_inc(x_1);
x_62 = l_Lake_cacheFileHash(x_1, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_io_metadata(x_1, x_64);
lean_dec(x_1);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_61);
x_80 = lean_array_push(x_61, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_62, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_85 = x_62;
} else {
 lean_dec_ref(x_62);
 x_85 = lean_box(0);
}
x_86 = lean_io_error_to_string(x_83);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_get_size(x_61);
x_90 = lean_array_push(x_61, x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_85;
 lean_ctor_set_tag(x_92, 0);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
lean_dec(x_11);
x_94 = l_Lake_replayBuildLog(x_10, x_93, x_12);
lean_dec(x_10);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lake_fetchFileTrace(x_1, x_4, x_97, x_96);
lean_dec(x_4);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_11);
lean_ctor_set(x_100, 1, x_12);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_11, 0);
x_102 = lean_ctor_get(x_11, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_11);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_12);
return x_104;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_2);
x_12 = lean_apply_3(x_1, x_2, x_8, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lake_BuildTrace_mix(x_11, x_15);
x_18 = lean_apply_1(x_3, x_10);
lean_inc(x_4);
x_19 = l_Lake_buildFileUnlessUpToDate(x_4, x_17, x_18, x_2, x_16, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_20, 0, x_7);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_7);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_19, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_ctor_get(x_20, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_43 = x_20;
} else {
 lean_dec_ref(x_20);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_7);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_12, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_12, 0, x_55);
return x_12;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_59 = x_13;
} else {
 lean_dec_ref(x_13);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
lean_inc(x_2);
x_68 = lean_apply_3(x_1, x_2, x_8, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lake_BuildTrace_mix(x_67, x_71);
x_74 = lean_apply_1(x_3, x_66);
lean_inc(x_4);
x_75 = l_Lake_buildFileUnlessUpToDate(x_4, x_73, x_74, x_2, x_72, x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_89 = x_76;
} else {
 lean_dec_ref(x_76);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_4);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_68, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_97 = x_68;
} else {
 lean_dec_ref(x_68);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_69, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_100 = x_69;
} else {
 lean_dec_ref(x_69);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_97;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_68, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_68, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_105 = x_68;
} else {
 lean_dec_ref(x_68);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_5);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_5);
lean_ctor_set(x_108, 1, x_6);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_5, 0);
x_110 = lean_ctor_get(x_5, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_5);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_6);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__1), 6, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_1);
x_8 = l_Task_Priority_default;
x_9 = 0;
x_10 = lean_io_map_task(x_7, x_2, x_8, x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_2);
x_12 = lean_apply_3(x_1, x_2, x_8, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lake_BuildTrace_mix(x_11, x_15);
x_18 = lean_apply_1(x_3, x_10);
lean_inc(x_4);
x_19 = l_Lake_buildFileUnlessUpToDate(x_4, x_17, x_18, x_2, x_16, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_20, 0, x_7);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_7);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_19, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_ctor_get(x_20, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_43 = x_20;
} else {
 lean_dec_ref(x_20);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_7);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_12, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_12, 0, x_55);
return x_12;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_59 = x_13;
} else {
 lean_dec_ref(x_13);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
lean_inc(x_2);
x_68 = lean_apply_3(x_1, x_2, x_8, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lake_BuildTrace_mix(x_67, x_71);
x_74 = lean_apply_1(x_3, x_66);
lean_inc(x_4);
x_75 = l_Lake_buildFileUnlessUpToDate(x_4, x_73, x_74, x_2, x_72, x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_89 = x_76;
} else {
 lean_dec_ref(x_76);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_4);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_68, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_97 = x_68;
} else {
 lean_dec_ref(x_68);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_69, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_100 = x_69;
} else {
 lean_dec_ref(x_69);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_97;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_68, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_68, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_105 = x_68;
} else {
 lean_dec_ref(x_68);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_5);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_5);
lean_ctor_set(x_108, 1, x_6);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_5, 0);
x_110 = lean_ctor_get(x_5, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_5);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_6);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildJob_collectList___rarg(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_io_map_task(x_10, x_8, x_11, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildJob_collectArray___rarg(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_io_map_task(x_10, x_8, x_11, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepArray___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildFileAfterDepArray___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildTrace_compute___at_Lake_fetchFileTrace___spec__1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_2);
x_20 = lean_array_push(x_2, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_io_error_to_string(x_22);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_2);
x_28 = lean_array_push(x_2, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
}
static lean_object* _init_l_Lake_inputFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lake_inputFile___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lake_inputFile___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Task_Priority_default;
x_7 = lean_io_as_task(x_5, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_inputFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_string_hash(x_6);
lean_dec(x_6);
x_8 = 1723;
x_9 = lean_uint64_mix_hash(x_8, x_7);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint64_t x_5; 
lean_dec(x_2);
x_5 = l_Lake_Hash_nil;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
uint64_t x_7; 
lean_dec(x_2);
x_7 = l_Lake_Hash_nil;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint64_t x_10; uint64_t x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lake_Hash_nil;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_buildO___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_62; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
lean_inc(x_5);
x_62 = lean_apply_3(x_6, x_5, x_10, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_68 = l_Lake_platformTrace;
x_69 = lean_uint64_mix_hash(x_67, x_68);
x_70 = l_Lake_buildO___lambda__1___closed__2;
x_71 = lean_box_uint64(x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lake_BuildTrace_mix(x_66, x_72);
lean_ctor_set(x_63, 0, x_73);
x_14 = x_63;
x_15 = x_64;
goto block_61;
}
else
{
lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_77 = l_Lake_platformTrace;
x_78 = lean_uint64_mix_hash(x_76, x_77);
x_79 = l_Lake_buildO___lambda__1___closed__2;
x_80 = lean_box_uint64(x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lake_BuildTrace_mix(x_74, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_14 = x_83;
x_15 = x_64;
goto block_61;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
lean_dec(x_62);
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
x_14 = x_63;
x_15 = x_84;
goto block_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_14 = x_88;
x_15 = x_84;
goto block_61;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_62);
if (x_89 == 0)
{
return x_62;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_62, 0);
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_62);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
block_61:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lake_BuildTrace_mix(x_12, x_16);
x_19 = l_Array_append___rarg(x_1, x_2);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lake_compileO___boxed), 7, 4);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_11);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_4);
lean_inc(x_3);
x_21 = l_Lake_buildFileUnlessUpToDate(x_3, x_18, x_20, x_5, x_17, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
if (lean_is_scalar(x_13)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_13;
}
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_22, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
if (lean_is_scalar(x_13)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_13;
}
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_35 = x_22;
} else {
 lean_dec_ref(x_22);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_13;
}
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_21, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_21, 0, x_44);
return x_21;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_48 = x_22;
} else {
 lean_dec_ref(x_22);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_13);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_15);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_15);
return x_60;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_7);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_7);
lean_ctor_set(x_94, 1, x_8);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_7, 0);
x_96 = lean_ctor_get(x_7, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_7);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_8);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__1), 8, 6);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_7);
lean_closure_set(x_9, 5, x_6);
x_10 = l_Task_Priority_default;
x_11 = 0;
x_12 = lean_io_map_task(x_9, x_2, x_10, x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___at_Lake_buildO___spec__1___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_4(x_2, x_9, x_3, x_10, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildLeanO___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Array_append___rarg(x_1, x_2);
x_10 = l_Lake_compileO(x_3, x_4, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_buildLeanO___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_14 = l_Lake_platformTrace;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lake_buildO___lambda__1___closed__2;
x_17 = lean_box_uint64(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lake_BuildTrace_mix(x_12, x_18);
x_20 = l_Lake_BuildTrace_mix(x_11, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__2___boxed), 8, 4);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_10);
x_22 = l_Lake_buildLeanO___lambda__3___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_4);
x_24 = l_Lake_buildFileUnlessUpToDate(x_4, x_20, x_23, x_1, x_8, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_25, 0, x_7);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_24, 0, x_32);
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_36 = x_25;
} else {
 lean_dec_ref(x_25);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_48 = x_25;
} else {
 lean_dec_ref(x_25);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_59 = l_Lake_platformTrace;
x_60 = lean_uint64_mix_hash(x_58, x_59);
x_61 = l_Lake_buildO___lambda__1___closed__2;
x_62 = lean_box_uint64(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lake_BuildTrace_mix(x_57, x_63);
x_65 = l_Lake_BuildTrace_mix(x_56, x_64);
lean_inc(x_4);
x_66 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__2___boxed), 8, 4);
lean_closure_set(x_66, 0, x_3);
lean_closure_set(x_66, 1, x_2);
lean_closure_set(x_66, 2, x_4);
lean_closure_set(x_66, 3, x_55);
x_67 = l_Lake_buildLeanO___lambda__3___closed__1;
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_66);
lean_inc(x_4);
x_69 = l_Lake_buildFileUnlessUpToDate(x_4, x_65, x_68, x_1, x_8, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__3), 6, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_1);
x_8 = l_Task_Priority_default;
x_9 = 0;
x_10 = lean_io_map_task(x_7, x_2, x_8, x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildLeanO___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanO___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_6, 11);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
static lean_object* _init_l_Lake_buildStaticLib___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lake_BuildTrace_nil;
x_11 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_compileStaticLib___boxed), 6, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_8);
x_13 = l_Lake_buildStaticLib___lambda__2___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
lean_inc(x_1);
x_15 = l_Lake_buildFileUnlessUpToDate(x_1, x_11, x_14, x_2, x_6, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_16, 0, x_5);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_27 = x_16;
} else {
 lean_dec_ref(x_16);
 x_27 = lean_box(0);
}
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_5, 0, x_1);
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_15, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_15, 0, x_35);
return x_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_39 = x_16;
} else {
 lean_dec_ref(x_16);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = l_Lake_BuildTrace_nil;
x_49 = l_Lake_BuildTrace_mix(x_47, x_48);
lean_inc(x_1);
x_50 = lean_alloc_closure((void*)(l_Lake_compileStaticLib___boxed), 6, 2);
lean_closure_set(x_50, 0, x_1);
lean_closure_set(x_50, 1, x_46);
x_51 = l_Lake_buildStaticLib___lambda__2___closed__1;
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_52, 0, x_51);
lean_closure_set(x_52, 1, x_50);
lean_inc(x_1);
x_53 = l_Lake_buildFileUnlessUpToDate(x_1, x_49, x_52, x_2, x_6, x_4);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_53, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_72 = x_53;
} else {
 lean_dec_ref(x_53);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_3);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_4);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_3);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_4);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildJob_collectArray___rarg(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__2), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
x_9 = l_Task_Priority_default;
x_10 = 0;
x_11 = lean_io_map_task(x_8, x_6, x_9, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildStaticLib___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildStaticLib(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_10, x_11, x_1);
x_13 = l_Array_append___rarg(x_12, x_2);
x_14 = l_Array_append___rarg(x_13, x_3);
x_15 = l_Lake_compileSharedLib(x_4, x_14, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_14 = l_Lake_platformTrace;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lake_buildO___lambda__1___closed__2;
x_17 = lean_box_uint64(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lake_BuildTrace_mix(x_12, x_18);
x_20 = l_Lake_BuildTrace_mix(x_11, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__1___boxed), 8, 4);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_4);
x_22 = l_Lake_buildLeanO___lambda__3___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_4);
x_24 = l_Lake_buildFileUnlessUpToDate(x_4, x_20, x_23, x_1, x_8, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_25, 0, x_7);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_24, 0, x_32);
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_36 = x_25;
} else {
 lean_dec_ref(x_25);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_48 = x_25;
} else {
 lean_dec_ref(x_25);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_59 = l_Lake_platformTrace;
x_60 = lean_uint64_mix_hash(x_58, x_59);
x_61 = l_Lake_buildO___lambda__1___closed__2;
x_62 = lean_box_uint64(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lake_BuildTrace_mix(x_57, x_63);
x_65 = l_Lake_BuildTrace_mix(x_56, x_64);
lean_inc(x_4);
x_66 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__1___boxed), 8, 4);
lean_closure_set(x_66, 0, x_55);
lean_closure_set(x_66, 1, x_3);
lean_closure_set(x_66, 2, x_2);
lean_closure_set(x_66, 3, x_4);
x_67 = l_Lake_buildLeanO___lambda__3___closed__1;
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_66);
lean_inc(x_4);
x_69 = l_Lake_buildFileUnlessUpToDate(x_4, x_65, x_68, x_1, x_8, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildJob_collectArray___rarg(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__2), 6, 4);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_io_map_task(x_10, x_8, x_11, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanSharedLib___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Array_append___rarg(x_1, x_2);
x_10 = l_Lake_compileExe(x_3, x_4, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_14 = l_Lake_platformTrace;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lake_buildO___lambda__1___closed__2;
x_17 = lean_box_uint64(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lake_BuildTrace_mix(x_12, x_18);
x_20 = l_Lake_BuildTrace_mix(x_11, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__1___boxed), 8, 4);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_10);
x_22 = l_Lake_buildLeanO___lambda__3___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_4);
x_24 = l_Lake_buildFileUnlessUpToDate(x_4, x_20, x_23, x_1, x_8, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_25, 0, x_7);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_24, 0, x_32);
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_36 = x_25;
} else {
 lean_dec_ref(x_25);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_48 = x_25;
} else {
 lean_dec_ref(x_25);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_59 = l_Lake_platformTrace;
x_60 = lean_uint64_mix_hash(x_58, x_59);
x_61 = l_Lake_buildO___lambda__1___closed__2;
x_62 = lean_box_uint64(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lake_BuildTrace_mix(x_57, x_63);
x_65 = l_Lake_BuildTrace_mix(x_56, x_64);
lean_inc(x_4);
x_66 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__1___boxed), 8, 4);
lean_closure_set(x_66, 0, x_3);
lean_closure_set(x_66, 1, x_2);
lean_closure_set(x_66, 2, x_4);
lean_closure_set(x_66, 3, x_55);
x_67 = l_Lake_buildLeanO___lambda__3___closed__1;
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_66);
lean_inc(x_4);
x_69 = l_Lake_buildFileUnlessUpToDate(x_4, x_65, x_68, x_1, x_8, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildJob_collectArray___rarg(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__2), 6, 4);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_io_map_task(x_10, x_8, x_11, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanExe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,--whole-archive", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1;
x_2 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,--no-whole-archive", 22);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,-force_load,", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_sharedLibExt;
lean_inc(x_9);
x_12 = l_System_FilePath_withExtension(x_9, x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_15 = l_Lake_platformTrace;
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = l_Lake_buildO___lambda__1___closed__2;
x_18 = lean_box_uint64(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lake_BuildTrace_mix(x_13, x_19);
x_21 = l_Lake_BuildTrace_mix(x_10, x_20);
x_22 = l_System_Platform_isOSX;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3;
x_24 = lean_array_push(x_23, x_9);
x_25 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4;
x_26 = lean_array_push(x_24, x_25);
x_27 = l_Array_append___rarg(x_26, x_3);
x_28 = l_Array_append___rarg(x_27, x_2);
lean_inc(x_12);
x_29 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_29, 0, x_12);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lake_buildLeanO___lambda__3___closed__1;
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_inc(x_12);
x_32 = l_Lake_buildFileUnlessUpToDate(x_12, x_21, x_31, x_1, x_7, x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_12);
lean_ctor_set(x_33, 0, x_6);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
lean_ctor_set(x_6, 1, x_38);
lean_ctor_set(x_6, 0, x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_42);
lean_ctor_set(x_6, 0, x_12);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_free_object(x_6);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_32, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_32, 0, x_52);
return x_32;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_56 = x_33;
} else {
 lean_dec_ref(x_33);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_12);
lean_free_object(x_6);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
return x_32;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_32, 0);
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_32);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5;
x_64 = lean_string_append(x_63, x_9);
lean_dec(x_9);
x_65 = l_Lake_replayBuildLog___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_Array_append___rarg(x_68, x_3);
x_70 = l_Array_append___rarg(x_69, x_2);
lean_inc(x_12);
x_71 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_71, 0, x_12);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lake_buildLeanO___lambda__3___closed__1;
x_73 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_71);
lean_inc(x_12);
x_74 = l_Lake_buildFileUnlessUpToDate(x_12, x_21, x_73, x_1, x_7, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_75, 0);
lean_ctor_set(x_6, 1, x_79);
lean_ctor_set(x_6, 0, x_12);
lean_ctor_set(x_75, 0, x_6);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 0);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_75);
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_12);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_6);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_74, 0, x_82);
return x_74;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec(x_74);
x_84 = lean_ctor_get(x_75, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_84);
lean_ctor_set(x_6, 0, x_12);
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_6);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_12);
lean_free_object(x_6);
x_89 = !lean_is_exclusive(x_74);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_74, 0);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_75);
if (x_91 == 0)
{
return x_74;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_75, 0);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_75);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_74, 0, x_94);
return x_74;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
lean_dec(x_74);
x_96 = lean_ctor_get(x_75, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_98 = x_75;
} else {
 lean_dec_ref(x_75);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_12);
lean_free_object(x_6);
x_101 = !lean_is_exclusive(x_74);
if (x_101 == 0)
{
return x_74;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_74, 0);
x_103 = lean_ctor_get(x_74, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_74);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_105 = lean_ctor_get(x_6, 0);
x_106 = lean_ctor_get(x_6, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_6);
x_107 = l_Lake_sharedLibExt;
lean_inc(x_105);
x_108 = l_System_FilePath_withExtension(x_105, x_107);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
x_110 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_111 = l_Lake_platformTrace;
x_112 = lean_uint64_mix_hash(x_110, x_111);
x_113 = l_Lake_buildO___lambda__1___closed__2;
x_114 = lean_box_uint64(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lake_BuildTrace_mix(x_109, x_115);
x_117 = l_Lake_BuildTrace_mix(x_106, x_116);
x_118 = l_System_Platform_isOSX;
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3;
x_120 = lean_array_push(x_119, x_105);
x_121 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4;
x_122 = lean_array_push(x_120, x_121);
x_123 = l_Array_append___rarg(x_122, x_3);
x_124 = l_Array_append___rarg(x_123, x_2);
lean_inc(x_108);
x_125 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_125, 0, x_108);
lean_closure_set(x_125, 1, x_124);
x_126 = l_Lake_buildLeanO___lambda__3___closed__1;
x_127 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_127, 0, x_126);
lean_closure_set(x_127, 1, x_125);
lean_inc(x_108);
x_128 = l_Lake_buildFileUnlessUpToDate(x_108, x_117, x_127, x_1, x_7, x_5);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_108);
lean_ctor_set(x_135, 1, x_132);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
if (lean_is_scalar(x_131)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_131;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_108);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_139 = x_128;
} else {
 lean_dec_ref(x_128);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_129, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_142 = x_129;
} else {
 lean_dec_ref(x_129);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_108);
x_145 = lean_ctor_get(x_128, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_147 = x_128;
} else {
 lean_dec_ref(x_128);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_149 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5;
x_150 = lean_string_append(x_149, x_105);
lean_dec(x_105);
x_151 = l_Lake_replayBuildLog___closed__2;
x_152 = lean_string_append(x_150, x_151);
x_153 = l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6;
x_154 = lean_array_push(x_153, x_152);
x_155 = l_Array_append___rarg(x_154, x_3);
x_156 = l_Array_append___rarg(x_155, x_2);
lean_inc(x_108);
x_157 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_157, 0, x_108);
lean_closure_set(x_157, 1, x_156);
x_158 = l_Lake_buildLeanO___lambda__3___closed__1;
x_159 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_159, 0, x_158);
lean_closure_set(x_159, 1, x_157);
lean_inc(x_108);
x_160 = l_Lake_buildFileUnlessUpToDate(x_108, x_117, x_159, x_1, x_7, x_5);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_166 = x_161;
} else {
 lean_dec_ref(x_161);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_108);
lean_ctor_set(x_167, 1, x_164);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_163;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_108);
x_170 = lean_ctor_get(x_160, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_171 = x_160;
} else {
 lean_dec_ref(x_160);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_161, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_174 = x_161;
} else {
 lean_dec_ref(x_161);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_108);
x_177 = lean_ctor_get(x_160, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_160, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_179 = x_160;
} else {
 lean_dec_ref(x_160);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_4);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_4);
lean_ctor_set(x_182, 1, x_5);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_4, 0);
x_184 = lean_ctor_get(x_4, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_4);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_5);
return x_186;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__1), 5, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
x_7 = l_Task_Priority_default;
x_8 = 0;
x_9 = lean_io_map_task(x_6, x_1, x_7, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("shared library `", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` has no file name", 18);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lib", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` does not start with `lib`; this is not supported on Unix", 58);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_9 = l_System_FilePath_fileStem(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
lean_dec(x_8);
x_10 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_7);
lean_dec(x_7);
x_12 = l_Lake_computeDynlibOfShared___lambda__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_6);
x_17 = lean_array_push(x_6, x_15);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_System_Platform_isWindows;
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lake_computeDynlibOfShared___lambda__1___closed__3;
lean_inc(x_19);
x_22 = l_String_startsWith(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_free_object(x_4);
lean_dec(x_8);
x_23 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_24 = lean_string_append(x_23, x_7);
lean_dec(x_7);
x_25 = l_Lake_computeDynlibOfShared___lambda__1___closed__4;
x_26 = lean_string_append(x_24, x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_6);
x_30 = lean_array_push(x_6, x_28);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_unsigned_to_nat(3u);
x_33 = l_String_drop(x_19, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_4, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_19);
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
lean_inc(x_39);
x_41 = l_System_FilePath_fileStem(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
x_42 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_43 = lean_string_append(x_42, x_39);
lean_dec(x_39);
x_44 = l_Lake_computeDynlibOfShared___lambda__1___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_38);
x_49 = lean_array_push(x_38, x_47);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_49);
lean_ctor_set(x_1, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = l_System_Platform_isWindows;
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lake_computeDynlibOfShared___lambda__1___closed__3;
lean_inc(x_51);
x_54 = l_String_startsWith(x_51, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_40);
x_55 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_56 = lean_string_append(x_55, x_39);
lean_dec(x_39);
x_57 = l_Lake_computeDynlibOfShared___lambda__1___closed__4;
x_58 = lean_string_append(x_56, x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_38);
x_62 = lean_array_push(x_38, x_60);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_unsigned_to_nat(3u);
x_65 = l_String_drop(x_51, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_39);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_40);
lean_ctor_set(x_1, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_39);
lean_ctor_set(x_69, 1, x_51);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_40);
lean_ctor_set(x_1, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
lean_inc(x_74);
x_77 = l_System_FilePath_fileStem(x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_76);
lean_dec(x_75);
x_78 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_79 = lean_string_append(x_78, x_74);
lean_dec(x_74);
x_80 = l_Lake_computeDynlibOfShared___lambda__1___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_get_size(x_73);
x_85 = lean_array_push(x_73, x_83);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_2);
return x_87;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
lean_dec(x_77);
x_89 = l_System_Platform_isWindows;
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lake_computeDynlibOfShared___lambda__1___closed__3;
lean_inc(x_88);
x_91 = l_String_startsWith(x_88, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_88);
lean_dec(x_76);
lean_dec(x_75);
x_92 = l_Lake_computeDynlibOfShared___lambda__1___closed__1;
x_93 = lean_string_append(x_92, x_74);
lean_dec(x_74);
x_94 = l_Lake_computeDynlibOfShared___lambda__1___closed__4;
x_95 = lean_string_append(x_93, x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_73);
x_99 = lean_array_push(x_73, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_2);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_unsigned_to_nat(3u);
x_103 = l_String_drop(x_88, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_74);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_76)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_76;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_75);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_73);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_2);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_74);
lean_ctor_set(x_108, 1, x_88);
if (lean_is_scalar(x_76)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_76;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_75);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_73);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_2);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_1);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_2);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_1);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_2);
return x_117;
}
}
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = l_Lake_computeDynlibOfShared___closed__1;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_io_map_task(x_4, x_1, x_5, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_computeDynlibOfShared(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_platformTrace___closed__1 = _init_l_Lake_platformTrace___closed__1();
l_Lake_platformTrace___closed__2 = _init_l_Lake_platformTrace___closed__2();
l_Lake_platformTrace = _init_l_Lake_platformTrace();
l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1();
l_Lake_fetchFileTrace___closed__1 = _init_l_Lake_fetchFileTrace___closed__1();
lean_mark_persistent(l_Lake_fetchFileTrace___closed__1);
l_Lake_replayBuildLog___closed__1 = _init_l_Lake_replayBuildLog___closed__1();
lean_mark_persistent(l_Lake_replayBuildLog___closed__1);
l_Lake_replayBuildLog___closed__2 = _init_l_Lake_replayBuildLog___closed__2();
lean_mark_persistent(l_Lake_replayBuildLog___closed__2);
l_Lake_replayBuildLog___closed__3 = _init_l_Lake_replayBuildLog___closed__3();
lean_mark_persistent(l_Lake_replayBuildLog___closed__3);
l_Lake_replayBuildLog___closed__4 = _init_l_Lake_replayBuildLog___closed__4();
lean_mark_persistent(l_Lake_replayBuildLog___closed__4);
l_Lake_replayBuildLog___closed__5 = _init_l_Lake_replayBuildLog___closed__5();
lean_mark_persistent(l_Lake_replayBuildLog___closed__5);
l_Lake_buildFileUnlessUpToDate___closed__1 = _init_l_Lake_buildFileUnlessUpToDate___closed__1();
lean_mark_persistent(l_Lake_buildFileUnlessUpToDate___closed__1);
l_Lake_buildFileUnlessUpToDate___closed__2 = _init_l_Lake_buildFileUnlessUpToDate___closed__2();
lean_mark_persistent(l_Lake_buildFileUnlessUpToDate___closed__2);
l_Lake_inputFile___closed__1 = _init_l_Lake_inputFile___closed__1();
lean_mark_persistent(l_Lake_inputFile___closed__1);
l_Lake_buildO___lambda__1___closed__1 = _init_l_Lake_buildO___lambda__1___closed__1();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__1);
l_Lake_buildO___lambda__1___closed__2 = _init_l_Lake_buildO___lambda__1___closed__2();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__2);
l_Lake_buildLeanO___lambda__3___closed__1 = _init_l_Lake_buildLeanO___lambda__3___closed__1();
lean_mark_persistent(l_Lake_buildLeanO___lambda__3___closed__1);
l_Lake_buildStaticLib___lambda__2___closed__1 = _init_l_Lake_buildStaticLib___lambda__2___closed__1();
lean_mark_persistent(l_Lake_buildStaticLib___lambda__2___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__2);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__3);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__4);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__5);
l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__1___closed__6);
l_Lake_computeDynlibOfShared___lambda__1___closed__1 = _init_l_Lake_computeDynlibOfShared___lambda__1___closed__1();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__1___closed__1);
l_Lake_computeDynlibOfShared___lambda__1___closed__2 = _init_l_Lake_computeDynlibOfShared___lambda__1___closed__2();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__1___closed__2);
l_Lake_computeDynlibOfShared___lambda__1___closed__3 = _init_l_Lake_computeDynlibOfShared___lambda__1___closed__3();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__1___closed__3);
l_Lake_computeDynlibOfShared___lambda__1___closed__4 = _init_l_Lake_computeDynlibOfShared___lambda__1___closed__4();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__1___closed__4);
l_Lake_computeDynlibOfShared___closed__1 = _init_l_Lake_computeDynlibOfShared___closed__1();
lean_mark_persistent(l_Lake_computeDynlibOfShared___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
