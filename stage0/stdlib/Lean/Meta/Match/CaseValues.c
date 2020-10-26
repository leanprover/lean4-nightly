// Lean compiler output
// Module: Lean.Meta.Match.CaseValues
// Imports: Init Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Clear
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
lean_object* l_Lean_Meta_caseValues_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__5;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__3;
lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_caseValues_loop_match__1(lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseValuesSubgoal_newHs___default;
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__6;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_caseValueAux_match__1(lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop_match__4(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__2;
lean_object* l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__8;
lean_object* l_Lean_Meta_CaseValuesSubgoal_subst___default;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__4;
lean_object* l_Lean_Meta_caseValues_loop___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux_match__3(lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__1;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseValueSubgoal_subst___default;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_516____closed__2;
lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__6;
lean_object* l_Lean_Meta_caseValues_loop___closed__3;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__5;
lean_object* l_Lean_Meta_caseValues_loop___closed__5;
lean_object* l_Lean_Meta_caseValues_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__5;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___at_Lean_Meta_mkDecideProof___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_caseValues_loop___closed__2;
lean_object* l_Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__6;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop___closed__6;
lean_object* l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop___closed__1;
lean_object* l_Lean_Meta_caseValues_loop_match__3(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_object* l_Lean_Meta_caseValue___closed__3;
lean_object* l_Lean_Meta_caseValues_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Meta_substCore___spec__8(lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1;
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop_match__2(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_caseValueAux_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_caseValueAux_match__2(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__4;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__3;
lean_object* l_Lean_Meta_caseValues_loop___closed__7;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__9;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__7;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues_loop_match__3___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_CaseValueSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseValueAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux_match__3___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found decl");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("searching for decl");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst domain: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_58; lean_object* x_59; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_st_ref_get(x_7, x_8);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = 0;
x_58 = x_75;
x_59 = x_74;
goto block_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
lean_inc(x_3);
x_77 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_3, x_4, x_5, x_6, x_7, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_58 = x_80;
x_59 = x_79;
goto block_69;
}
block_57:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_10 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
x_43 = lean_st_ref_get(x_7, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_12 = x_47;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
lean_inc(x_3);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_3, x_4, x_5, x_6, x_7, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_12 = x_52;
goto block_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Lean_Meta_caseValueAux___lambda__1___closed__4;
lean_inc(x_3);
x_55 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_3, x_54, x_4, x_5, x_6, x_7, x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_12 = x_56;
goto block_42;
}
}
block_42:
{
lean_object* x_13; 
lean_inc(x_4);
x_13 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
lean_inc(x_3);
x_26 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_3, x_4, x_5, x_6, x_7, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_caseValueAux___lambda__1___closed__2;
x_37 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_3, x_36, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_4);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_69:
{
if (x_58 == 0)
{
x_9 = x_59;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = l_Lean_Meta_FVarSubst_domain(x_1);
x_61 = l_List_map___at_Lean_Meta_substCore___spec__8(x_60);
x_62 = l_Lean_MessageData_ofList(x_61);
lean_dec(x_61);
x_63 = l_Lean_Meta_caseValueAux___lambda__1___closed__6;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_3);
x_67 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_3, x_66, x_4, x_5, x_6, x_7, x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_9 = x_68;
goto block_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValue");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__2___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dite");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__2___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarTag(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Meta_checkNotAssigned(x_1, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_mkFVar(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_20, x_3, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_caseValueAux___lambda__2___closed__5;
lean_inc(x_22);
x_25 = l_Lean_mkApp(x_24, x_22);
x_26 = 0;
lean_inc(x_18);
lean_inc(x_22);
lean_inc(x_4);
x_27 = l_Lean_mkForall(x_4, x_26, x_22, x_18);
x_28 = l_Lean_mkForall(x_4, x_26, x_25, x_18);
lean_inc(x_6);
lean_inc(x_12);
x_29 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_27, x_12, x_6, x_7, x_8, x_9, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_6);
x_32 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_28, x_12, x_6, x_7, x_8, x_9, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_22);
lean_inc(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_30);
lean_inc(x_33);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = l_Lean_Meta_caseValueAux___lambda__2___closed__9;
x_40 = lean_array_push(x_39, x_36);
x_41 = lean_array_push(x_40, x_35);
x_42 = lean_array_push(x_41, x_37);
x_43 = lean_array_push(x_42, x_38);
x_44 = l_Lean_Meta_caseValueAux___lambda__2___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_mkAppOptM___at_Lean_Meta_mkDecideProof___spec__2(x_44, x_43, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_46, x_6, x_7, x_8, x_9, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_51 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = l_Lean_Meta_intro1Core(x_50, x_51, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_5);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_5);
x_58 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_59 = l_Lean_Meta_intro1Core(x_58, x_51, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
x_65 = l_Lean_Meta_substCore(x_63, x_62, x_64, x_5, x_64, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 1);
x_71 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_516____closed__2;
lean_inc(x_62);
lean_inc(x_69);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 8, 3);
lean_closure_set(x_72, 0, x_69);
lean_closure_set(x_72, 1, x_62);
lean_closure_set(x_72, 2, x_71);
lean_inc(x_70);
x_73 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_70, x_72, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = l_Lean_Meta_FVarSubst_get(x_69, x_62);
x_77 = l_Lean_Expr_fvarId_x21(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_69);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 0, x_78);
lean_ctor_set(x_73, 0, x_66);
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_80 = l_Lean_Meta_FVarSubst_get(x_69, x_62);
x_81 = l_Lean_Expr_fvarId_x21(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_69);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 0, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_66);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_66);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_57);
x_84 = !lean_is_exclusive(x_73);
if (x_84 == 0)
{
return x_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_73, 0);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_73);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_66, 0);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_66);
x_90 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_516____closed__2;
lean_inc(x_62);
lean_inc(x_88);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 8, 3);
lean_closure_set(x_91, 0, x_88);
lean_closure_set(x_91, 1, x_62);
lean_closure_set(x_91, 2, x_90);
lean_inc(x_89);
x_92 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_89, x_91, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Meta_FVarSubst_get(x_88, x_62);
x_96 = l_Lean_Expr_fvarId_x21(x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_88);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_57);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_62);
lean_dec(x_57);
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_102 = x_92;
} else {
 lean_dec_ref(x_92);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_104 = !lean_is_exclusive(x_65);
if (x_104 == 0)
{
return x_65;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_65, 0);
x_106 = lean_ctor_get(x_65, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_65);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_108 = !lean_is_exclusive(x_59);
if (x_108 == 0)
{
return x_59;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_59, 0);
x_110 = lean_ctor_get(x_59, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_59);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_112 = !lean_is_exclusive(x_52);
if (x_112 == 0)
{
return x_52;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_52, 0);
x_114 = lean_ctor_get(x_52, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_52);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_45);
if (x_116 == 0)
{
return x_45;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_45, 0);
x_118 = lean_ctor_get(x_45, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_45);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_21);
if (x_120 == 0)
{
return x_21;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_21, 0);
x_122 = lean_ctor_get(x_21, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_21);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_17);
if (x_124 == 0)
{
return x_17;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_17, 0);
x_126 = lean_ctor_get(x_17, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_17);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_15);
if (x_128 == 0)
{
return x_15;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_15, 0);
x_130 = lean_ctor_get(x_15, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_15);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_11);
if (x_132 == 0)
{
return x_11;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_11, 0);
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_11);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* l_Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__2), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_caseValueAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("thenBranch");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elseBranch");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_caseValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_caseValueAux(x_1, x_2, x_3, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_caseValue___closed__4;
x_17 = l_Lean_Meta_appendTagSuffix(x_15, x_16, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_caseValue___closed__6;
x_22 = l_Lean_Meta_appendTagSuffix(x_20, x_21, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CaseValuesSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValues_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValues_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValues_loop_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; 
lean_dec(x_7);
x_8 = lean_apply_4(x_6, x_1, x_2, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_6(x_7, x_1, x_2, x_9, x_10, x_4, x_5);
return x_11;
}
}
}
lean_object* l_Lean_Meta_caseValues_loop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValues_loop_match__4___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Meta_FVarSubst_get(x_17, x_14);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_tryClear(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_16;
x_5 = x_21;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_18);
x_4 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValues");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("list of values must not be empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_caseValues_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_caseValues_loop___closed__2;
x_14 = l_Lean_Meta_caseValues_loop___closed__5;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_4, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Name_appendIndexAfter(x_2, x_3);
x_20 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_21 = l_Lean_Meta_caseValueAux(x_4, x_1, x_17, x_19, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc(x_28);
x_29 = l_Lean_Meta_caseValues_loop___closed__7;
lean_inc(x_3);
x_30 = l_Lean_Name_appendIndexAfter(x_29, x_3);
lean_inc(x_26);
x_31 = l_Lean_Meta_appendTagSuffix(x_26, x_30, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1(x_6, x_23, x_6, x_33, x_26, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_27);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_28);
x_40 = lean_array_push(x_7, x_39);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_45 = l_Lean_Name_appendIndexAfter(x_29, x_44);
lean_inc(x_41);
x_46 = l_Lean_Meta_appendTagSuffix(x_41, x_45, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_array_push(x_6, x_42);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_20);
x_51 = lean_array_push(x_40, x_50);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_array_push(x_6, x_42);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_20);
x_55 = lean_array_push(x_40, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_3, x_61);
lean_dec(x_3);
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_dec(x_25);
x_65 = lean_array_push(x_6, x_64);
x_3 = x_62;
x_4 = x_63;
x_5 = x_18;
x_6 = x_65;
x_7 = x_40;
x_12 = x_36;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
return x_31;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_31, 0);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_31);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
lean_object* l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___at_Lean_Meta_caseValues_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_caseValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_toList___rarg(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Array_empty___closed__1;
x_13 = l_Lean_Meta_caseValues_loop(x_2, x_4, x_11, x_1, x_10, x_12, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Meta_caseValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_caseValues(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match_CaseValues(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CaseValueSubgoal_subst___default = _init_l_Lean_Meta_CaseValueSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_subst___default);
l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1 = _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1___closed__1);
l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1 = _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__1);
l_Lean_Meta_caseValueAux___lambda__1___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__1);
l_Lean_Meta_caseValueAux___lambda__1___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__2);
l_Lean_Meta_caseValueAux___lambda__1___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__3);
l_Lean_Meta_caseValueAux___lambda__1___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__4);
l_Lean_Meta_caseValueAux___lambda__1___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__5);
l_Lean_Meta_caseValueAux___lambda__1___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__6);
l_Lean_Meta_caseValueAux___lambda__2___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__1);
l_Lean_Meta_caseValueAux___lambda__2___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__2);
l_Lean_Meta_caseValueAux___lambda__2___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__3);
l_Lean_Meta_caseValueAux___lambda__2___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__4);
l_Lean_Meta_caseValueAux___lambda__2___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__5);
l_Lean_Meta_caseValueAux___lambda__2___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__6);
l_Lean_Meta_caseValueAux___lambda__2___closed__7 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__7);
l_Lean_Meta_caseValueAux___lambda__2___closed__8 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__8);
l_Lean_Meta_caseValueAux___lambda__2___closed__9 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__9);
l_Lean_Meta_caseValue___closed__1 = _init_l_Lean_Meta_caseValue___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__1);
l_Lean_Meta_caseValue___closed__2 = _init_l_Lean_Meta_caseValue___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__2);
l_Lean_Meta_caseValue___closed__3 = _init_l_Lean_Meta_caseValue___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__3);
l_Lean_Meta_caseValue___closed__4 = _init_l_Lean_Meta_caseValue___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__4);
l_Lean_Meta_caseValue___closed__5 = _init_l_Lean_Meta_caseValue___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__5);
l_Lean_Meta_caseValue___closed__6 = _init_l_Lean_Meta_caseValue___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__6);
l_Lean_Meta_CaseValuesSubgoal_newHs___default = _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default();
lean_mark_persistent(l_Lean_Meta_CaseValuesSubgoal_newHs___default);
l_Lean_Meta_CaseValuesSubgoal_subst___default = _init_l_Lean_Meta_CaseValuesSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_CaseValuesSubgoal_subst___default);
l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1 = _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2___closed__1);
l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2 = _init_l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Match_CaseValues___instance__2);
l_Lean_Meta_caseValues_loop___closed__1 = _init_l_Lean_Meta_caseValues_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__1);
l_Lean_Meta_caseValues_loop___closed__2 = _init_l_Lean_Meta_caseValues_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__2);
l_Lean_Meta_caseValues_loop___closed__3 = _init_l_Lean_Meta_caseValues_loop___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__3);
l_Lean_Meta_caseValues_loop___closed__4 = _init_l_Lean_Meta_caseValues_loop___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__4);
l_Lean_Meta_caseValues_loop___closed__5 = _init_l_Lean_Meta_caseValues_loop___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__5);
l_Lean_Meta_caseValues_loop___closed__6 = _init_l_Lean_Meta_caseValues_loop___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__6);
l_Lean_Meta_caseValues_loop___closed__7 = _init_l_Lean_Meta_caseValues_loop___closed__7();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
