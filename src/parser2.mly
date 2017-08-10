/**************************************************************************/
/*     Sail                                                               */
/*                                                                        */
/*  Copyright (c) 2013-2017                                               */
/*    Kathyrn Gray                                                        */
/*    Shaked Flur                                                         */
/*    Stephen Kell                                                        */
/*    Gabriel Kerneis                                                     */
/*    Robert Norton-Wright                                                */
/*    Christopher Pulte                                                   */
/*    Peter Sewell                                                        */
/*                                                                        */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/**************************************************************************/

%{

let r = fun x -> x (* Ulib.Text.of_latin1 *)

open Parse_ast

let loc n m = Range (m, n)

let mk_id i n m = Id_aux (i, loc m n)
let mk_kid str n m = Kid_aux (Var str, loc n m)

let deinfix (Id_aux (Id v, l)) = Id_aux (DeIid v, l)

let mk_typ t n m = ATyp_aux (t, loc n m)
let mk_pat p n m = P_aux (p, loc n m)
let mk_pexp p n m = Pat_aux (p, loc n m)
let mk_exp e n m = E_aux (e, loc n m)
let mk_lit l n m = L_aux (l, loc n m)
let mk_lit_exp l n m = mk_exp (E_lit (mk_lit l n m)) n m
let mk_typschm tq t n m = TypSchm_aux (TypSchm_ts (tq, t), loc n m)
let mk_nc nc n m = NC_aux (nc, loc n m)

let mk_funcl f n m = FCL_aux (f, loc n m)
let mk_fun fn n m = FD_aux (fn, loc n m)
let mk_td t n m = TD_aux (t, loc n m)
let mk_vs v n m = VS_aux (v, loc n m)

let qi_id_of_kopt (KOpt_aux (kopt_aux, l) as kopt) = QI_aux (QI_id kopt, l)

let mk_recn = (Rec_aux((Rec_nonrec), Unknown))
let mk_typqn = (TypQ_aux(TypQ_no_forall,Unknown))
let mk_tannotn = Typ_annot_opt_aux(Typ_annot_opt_none,Unknown)
let mk_eannotn = Effect_opt_aux(Effect_opt_pure,Unknown)
let mk_namesectn = Name_sect_aux(Name_sect_none,Unknown)

type lchain =
  LC_lt
| LC_lteq
| LC_nexp of atyp

let rec desugar_lchain chain s e =
  match chain with
  | [LC_nexp n1; LC_lteq; LC_nexp n2] ->
    mk_nc (NC_bounded_le (n1, n2)) s e
  | [LC_nexp n1; LC_lt; LC_nexp n2] ->
    mk_nc (NC_bounded_le (mk_typ (ATyp_sum (n1, mk_typ (ATyp_constant 1) s e)) s e, n2)) s e
  | (LC_nexp n1 :: LC_lteq :: LC_nexp n2 :: chain) ->
    let nc1 = mk_nc (NC_bounded_le (n1, n2)) s e in
    mk_nc (NC_and (nc1, desugar_lchain (LC_nexp n2 :: chain) s e)) s e
  | (LC_nexp n1 :: LC_lt :: LC_nexp n2 :: chain) ->
    let nc1 = mk_nc (NC_bounded_le (mk_typ (ATyp_sum (n1, mk_typ (ATyp_constant 1) s e)) s e, n2)) s e in
    mk_nc (NC_and (nc1, desugar_lchain (LC_nexp n2 :: chain) s e)) s e
  | _ -> assert false

type rchain =
  RC_gt
| RC_gteq
| RC_nexp of atyp

let rec desugar_rchain chain s e =
  match chain with
  | [RC_nexp n1; RC_gteq; RC_nexp n2] ->
    mk_nc (NC_bounded_ge (n1, n2)) s e
  | [RC_nexp n1; RC_gt; RC_nexp n2] ->
    mk_nc (NC_bounded_ge (n1, mk_typ (ATyp_sum (n2, mk_typ (ATyp_constant 1) s e)) s e)) s e
  | (RC_nexp n1 :: RC_gteq :: RC_nexp n2 :: chain) ->
    let nc1 = mk_nc (NC_bounded_ge (n1, n2)) s e in
    mk_nc (NC_and (nc1, desugar_rchain (RC_nexp n2 :: chain) s e)) s e
  | (RC_nexp n1 :: RC_gt :: RC_nexp n2 :: chain) ->
    let nc1 = mk_nc (NC_bounded_ge (n1, mk_typ (ATyp_sum (n2, mk_typ (ATyp_constant 1) s e)) s e)) s e in
    mk_nc (NC_and (nc1, desugar_rchain (RC_nexp n2 :: chain) s e)) s e
  | _ -> assert false

%}

/*Terminals with no content*/

%token And As Assert Bitzero Bitone Bits By Match Clause Const Dec Def Default Deinfix Effect EFFECT End Op
%token Enum Else Exit Extern False Forall Exist Foreach Overload Function_ If_ In IN Inc Let_ Member Int Order Cast
%token Pure Rec Register Return Scattered Sizeof Struct Switch Then True TwoStarStar Type TYPE Typedef
%token Undefined Union With When Val Constraint
%token Barr Depend Rreg Wreg Rmem Rmemt Wmem Wmv Wmvt Eamem Exmem Undef Unspec Nondet Escape

%nonassoc Then
%nonassoc Else

%token Div_ Mod ModUnderS Quot Rem QuotUnderS

%token Bar Comma Dot Eof Minus Semi Under
%token Lcurly Rcurly Lparen Rparen Lsquare Rsquare
%token BarBar BarSquare BarBarSquare ColonEq ColonGt ColonSquare DotDot
%token MinusGt LtBar LtColon SquareBar SquareBarBar SquareColon

/*Terminals with content*/

%token <string> Id TyVar Decl TyDecl
%token <int> Num
%token <string> String Bin Hex Real

%token <string> Amp At Carrot  Div Eq Excl Gt Lt Plus Star Tilde EqGt Unit
%token <string> Colon ExclEq
%token <string> GtEq GtEqPlus GtGt GtGtGt GtPlus HashGtGt HashLtLt
%token <string> LtEq LtEqPlus LtGt LtLt LtLtLt LtPlus StarStar TildeCarrot

%token <string> GtEqUnderS GtEqUnderSi GtEqUnderU GtEqUnderUi GtGtUnderU GtUnderS
%token <string> GtUnderSi GtUnderU GtUnderUi LtEqUnderS LtEqUnderSi LtEqUnderU
%token <string> LtEqUnderUi LtUnderS LtUnderSi LtUnderU LtUnderUi StarStarUnderS StarStarUnderSi StarUnderS
%token <string> StarUnderSi StarUnderU StarUnderUi TwoCarrot PlusUnderS MinusUnderS

%token <string> Op0 Op1 Op2 Op3 Op4 Op5 Op6 Op7 Op8 Op9

%start file
%type <Parse_ast.defs> defs
%type <Parse_ast.defs> file

%%

id:
  | Id
    { mk_id (Id $1) $startpos $endpos }
  | Op Op1
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op2
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op3
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op4
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op5
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op6
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op7
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op8
    { mk_id (DeIid $2) $startpos $endpos }
  | Op Op9
    { mk_id (DeIid $2) $startpos $endpos }

op0: Op0 { mk_id (Id $1) $startpos $endpos }
op1: Op1 { mk_id (Id $1) $startpos $endpos }
op2: Op2 { mk_id (Id $1) $startpos $endpos }
op3: Op3 { mk_id (Id $1) $startpos $endpos }
op4: Op4 { mk_id (Id $1) $startpos $endpos }
op5: Op5 { mk_id (Id $1) $startpos $endpos }
op6: Op6 { mk_id (Id $1) $startpos $endpos }
op7: Op7 { mk_id (Id $1) $startpos $endpos }
op8: Op8 { mk_id (Id $1) $startpos $endpos }
op9: Op9 { mk_id (Id $1) $startpos $endpos }

decl:
  | Decl
    { mk_id (Id $1) $startpos $endpos }

kid:
  | TyVar
    { mk_kid $1 $startpos $endpos }

tydecl:
  | TyDecl
    { mk_kid $1 $startpos $endpos }

kid_list:
  | kid
    { [$1] }
  | kid kid_list
    { $1 :: $2 }

nc:
  | nc Bar nc_and
    { mk_nc (NC_or ($1, $3)) $startpos $endpos }
  | nc_and
    { $1 }

nc_and:
  | nc_and Amp atomic_nc
    { mk_nc (NC_and ($1, $3)) $startpos $endpos }
  | atomic_nc
    { $1 }

atomic_nc:
  | True
    { mk_nc NC_true $startpos $endpos }
  | False
    { mk_nc NC_false $startpos $endpos }
  | typ Eq typ
    { mk_nc (NC_fixed ($1, $3)) $startpos $endpos }
  | typ ExclEq typ
    { mk_nc (NC_not_equal ($1, $3)) $startpos $endpos }
  | nc_lchain
    { desugar_lchain $1 $startpos $endpos }
  | nc_rchain
    { desugar_rchain $1 $startpos $endpos }
  | Lparen nc Rparen
    { $2 }
  | kid In Lcurly num_list Rcurly
    { mk_nc (NC_nat_set_bounded ($1, $4)) $startpos $endpos }

num_list:
  | Num
    { [$1] }
  | Num Comma num_list
    { $1 :: $3 }

nc_lchain:
  | typ LtEq typ
    { [LC_nexp $1; LC_lteq; LC_nexp $3] }
  | typ Lt typ
    { [LC_nexp $1; LC_lt; LC_nexp $3] }
  | typ LtEq nc_lchain
    { LC_nexp $1 :: LC_lteq :: $3 }
  | typ Lt nc_lchain
    { LC_nexp $1 :: LC_lt :: $3 }

nc_rchain:
  | typ GtEq typ
    { [RC_nexp $1; RC_gteq; RC_nexp $3] }
  | typ Gt typ
    { [RC_nexp $1; RC_gt; RC_nexp $3] }
  | typ GtEq nc_rchain
    { RC_nexp $1 :: RC_gteq :: $3 }
  | typ Gt nc_rchain
    { RC_nexp $1 :: RC_gt :: $3 }

typ:
  | typ0
    { $1 }
  | Lparen typ Comma typ_list Rparen
    { mk_typ (ATyp_tup ($2 :: $4)) $startpos $endpos }
  | Lcurly kid_list Dot typ Rcurly
    { mk_typ (ATyp_exist ($2, NC_aux (NC_true, loc $startpos $endpos), $4)) $startpos $endpos }
  | Lcurly kid_list Comma nc Dot typ Rcurly
    { mk_typ (ATyp_exist ($2, $4, $6)) $startpos $endpos }

typ0:
  | typ1 op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }

typ1:
  | typ2 op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }

typ2:
  | typ3 op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 { $1 }

typ3:
  | typ4 op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 { $1 }

typ4:
  | typ5 op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 { $1 }

typ5:
  | typ6 op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }

typ6:
  | typ7 op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 { $1 }

typ7:
  | typ8 op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 { $1 }

typ8:
  | typ9 op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9 { $1 }

typ9:
  | atomic_typ op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }

atomic_typ:
  | id
    { mk_typ (ATyp_id $1) $startpos $endpos }
  | kid
    { mk_typ (ATyp_var $1) $startpos $endpos }
  | Num
    { mk_typ (ATyp_constant $1) $startpos $endpos }
  | Dec
    { mk_typ ATyp_dec $startpos $endpos }
  | Inc
    { mk_typ ATyp_inc $startpos $endpos }
  | id Lparen typ_list Rparen
    { mk_typ (ATyp_app ($1, $3)) $startpos $endpos }
  | Lparen typ Rparen
    { $2 }

typ_list:
  | typ
    { [$1] }
  | typ Comma typ_list
    { $1 :: $3 }

base_kind:
  | Int
    { BK_aux (BK_nat, loc $startpos $endpos) }
  | TYPE
    { BK_aux (BK_type, loc $startpos $endpos) }
  | Order
    { BK_aux (BK_order, loc $startpos $endpos) }

kind:
  | base_kind
    { K_aux (K_kind [$1], loc $startpos $endpos) }

kopt:
  | tydecl kind
    { KOpt_aux (KOpt_kind ($2, $1), loc $startpos $endpos) }
  | Lparen kid Colon kind Rparen
    { KOpt_aux (KOpt_kind ($4, $2), loc $startpos $endpos) }
  | kid
    { KOpt_aux (KOpt_none $1, loc $startpos $endpos) }

kopt_list:
  | kopt
    { [$1] }
  | kopt kopt_list
    { $1 :: $2 }

typquant:
  | kopt_list Comma nc
    { let qi_nc = QI_aux (QI_const $3, loc $startpos($3) $endpos($3)) in
      TypQ_aux (TypQ_tq (List.map qi_id_of_kopt $1 @ [qi_nc]), loc $startpos $endpos) }
  | kopt_list
    { TypQ_aux (TypQ_tq (List.map qi_id_of_kopt $1), loc $startpos $endpos) }

typschm:
  | typ MinusGt typ
    { (fun s e -> mk_typschm mk_typqn (mk_typ (ATyp_fn ($1, $3, mk_typ (ATyp_set []) s e)) s e) s e) $startpos $endpos }
  | Forall typquant Dot typ MinusGt typ
    { (fun s e -> mk_typschm $2 (mk_typ (ATyp_fn ($4, $6, mk_typ (ATyp_set []) s e)) s e) s e) $startpos $endpos }

pat:
  | atomic_pat
    { $1 }
  | atomic_pat As id
    { mk_pat (P_as ($1, $3)) $startpos $endpos }
  | Lparen pat Comma pat_list Rparen
    { mk_pat (P_tup ($2 :: $4)) $startpos $endpos }

pat_list:
  | pat
    { [$1] }
  | pat Comma pat_list
    { $1 :: $3 }

atomic_pat:
  | Under
    { mk_pat (P_wild) $startpos $endpos }
  | lit
    { mk_pat (P_lit $1) $startpos $endpos }
  | id
    { mk_pat (P_id $1) $startpos $endpos }
  | pat Colon typ
    { mk_pat (P_typ ($3, $1)) $startpos $endpos }
  | decl typ
    { mk_pat (P_typ ($2, mk_pat (P_id $1) $startpos $endpos($1))) $startpos $endpos }
  | Lparen pat Rparen
    { $2 }

lit:
  | True
    { mk_lit L_true $startpos $endpos }
  | False
    { mk_lit L_false $startpos $endpos }
  | Unit
    { mk_lit L_unit $startpos $endpos }
  | Num
    { mk_lit (L_num $1) $startpos $endpos }
  | Undefined
    { mk_lit L_undef $startpos $endpos }

exp:
  | cast_exp Colon typ
    { mk_exp (E_cast ($3, $1)) $startpos $endpos }
  | cast_exp
    { $1 }

cast_exp:
  | atomic_exp
    { $1 }
  | atomic_exp Eq cast_exp
    { mk_exp (E_assign ($1, $3)) $startpos $endpos }
  | Let_ letbind In cast_exp
    { mk_exp (E_let ($2, $4)) $startpos $endpos }
  | Lcurly block Rcurly
    { mk_exp (E_block $2) $startpos $endpos }
  | Return cast_exp
    { mk_exp (E_return $2) $startpos $endpos }
  | If_ exp Then cast_exp Else cast_exp
    { mk_exp (E_if ($2, $4, $6)) $startpos $endpos }
  | Match atomic_exp Lcurly case_list Rcurly
    { mk_exp (E_case ($2, $4)) $startpos $endpos }
  | Lparen exp Comma exp_list Rparen
    { mk_exp (E_tuple ($2 :: $4)) $startpos $endpos }

case:
  | pat EqGt exp
    { mk_pexp (Pat_exp ($1, $3)) $startpos $endpos }
  | pat If_ exp EqGt exp
    { mk_pexp (Pat_when ($1, $3, $5)) $startpos $endpos }

case_list:
  | case
    { [$1] }
  | case Comma case_list
    { $1 :: $3 }

block:
  | exp
    { [$1] }
  | If_ exp Then exp Semi block
    { mk_exp (E_if ($2, $4, mk_lit_exp L_unit $startpos($5) $endpos($5))) $startpos $endpos($5) :: $6 }
  | Let_ letbind Semi block
    { [mk_exp (E_let ($2, mk_exp (E_block $4) $startpos($4) $endpos)) $startpos $endpos] }
  | exp Semi /* Allow trailing semicolon in block */
    { [$1] }
  | exp Semi block
    { $1 :: $3 }

%inline letbind:
  | pat Eq exp
    { LB_aux (LB_val_implicit ($1, $3), loc $startpos $endpos) }

atomic_exp:
  | lit
    { mk_exp (E_lit $1) $startpos $endpos }
  | decl typ
    { mk_exp (E_cast ($2, mk_exp (E_id $1) $startpos $endpos($1))) $startpos $endpos }
  | id
    { mk_exp (E_id $1) $startpos $endpos }
  | id Unit
    { mk_exp (E_app ($1, [mk_lit_exp L_unit $startpos($2) $endpos])) $startpos $endpos }
  | id Lparen exp_list Rparen
    { mk_exp (E_app ($1, $3)) $startpos $endpos }
  | Lparen exp Rparen
    { $2 }

exp_list:
  | exp
    { [$1] }
  | exp Comma exp_list
    { $1 :: $3 }

cast_exp_list:
  | cast_exp
    { [$1] }
  | cast_exp Comma exp_list
    { $1 :: $3 }

funcl:
  | id pat Eq exp
    { mk_funcl (FCL_Funcl ($1, $2, $4)) $startpos $endpos }

type_def:
  | Typedef id typquant Eq typ
    { mk_td (TD_abbrev ($2, mk_namesectn, mk_typschm $3 $5 $startpos($3) $endpos)) $startpos $endpos }
  | Typedef id Eq typ
    { mk_td (TD_abbrev ($2, mk_namesectn, mk_typschm mk_typqn $4 $startpos($4) $endpos)) $startpos $endpos }
  | Struct id typquant Eq Lcurly struct_fields Rcurly
    { mk_td (TD_record ($2, mk_namesectn, $3, $6, false)) $startpos $endpos }
  | Enum id Eq enum_bar
    { mk_td (TD_enum ($2, mk_namesectn, $4, false)) $startpos $endpos }
  | Enum id Eq Lcurly enum Rcurly
    { mk_td (TD_enum ($2, mk_namesectn, $5, false)) $startpos $endpos }
  | Union id typquant Eq Lcurly type_unions Rcurly
    { mk_td (TD_variant ($2, mk_namesectn, $3, $6, false)) $startpos $endpos }

enum_bar:
  | id
    { [$1] }
  | id Bar enum_bar
    { $1 :: $3 }

enum:
  | id
    { [$1] }
  | id Comma enum
    { $1 :: $3 }

struct_field:
  | decl typ
    { ($2, $1) }
  | id Colon typ
    { ($3, $1) }

struct_fields:
  | struct_field
    { [$1] }
  | struct_field Comma
    { [$1] }
  | struct_field Comma struct_fields
    { $1 :: $3 }

type_union:
  | decl typ
    { Tu_aux (Tu_ty_id ($2, $1), loc $startpos $endpos) }
  | id Colon typ
    { Tu_aux (Tu_ty_id ($3, $1), loc $startpos $endpos) }
  | id
    { Tu_aux (Tu_id $1, loc $startpos $endpos) }

type_unions:
  | type_union
    { [$1] }
  | type_union Comma
    { [$1] }
  | type_union Comma type_unions
    { $1 :: $3 }

fun_def:
  | Function_ funcl
    { mk_fun (FD_function (mk_recn, mk_tannotn, mk_eannotn, [$2])) $startpos $endpos }

let_def:
  | Let_ letbind
    { $2 }

val_spec_def:
  | Val decl typschm
    { mk_vs (VS_val_spec ($3, $2)) $startpos $endpos }
  | Val id Colon typschm
    { mk_vs (VS_val_spec ($4, $2)) $startpos $endpos }

def:
  | fun_def
    { DEF_fundef $1 }
  | val_spec_def
    { DEF_spec $1 }
  | type_def
    { DEF_type $1 }
  | let_def
    { DEF_val $1 }

defs_list:
  | def
    { [$1] }
  | def defs_list
    { $1::$2 }

defs:
  | defs_list
    { (Defs $1) }

file:
  | defs Eof
    { $1 }

