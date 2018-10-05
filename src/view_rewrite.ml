(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open Type_check
open Rewriter

let rewrite_view_patterns =
  let view_count = ref 0 in
  let gen_view_id () = incr view_count; mk_id ("_view_" ^ string_of_int !view_count) in

  let view_guard annot view id pat =
    let guard = mk_exp (E_case (mk_exp (E_cast (pat_typ_of pat,
                                                mk_exp (E_app (view, [mk_exp (E_id id)])))),
                                [mk_pexp (Pat_exp (strip_pat pat, mk_lit_exp L_true));
                                 mk_pexp (Pat_exp (mk_pat P_wild, mk_lit_exp L_false))]))
    in
    check_exp (Env.add_local id (Immutable, typ_of_annot annot) (env_of_annot annot)) guard bool_typ
  in
  let view_let annot view id pat (E_aux (_, exp_annot) as exp) =
    let view_call =
      mk_exp (E_cast (pat_typ_of pat, mk_exp (E_app (view, [mk_exp (E_id id)]))))
      |> infer_exp (Env.add_local id (Immutable, typ_of_annot annot) (env_of_annot annot))
    in
    E_aux (E_let (LB_aux (LB_val (pat, view_call), (Parse_ast.Unknown, empty_tannot)), exp), exp_annot)
  in

  let guards = ref [] in
  let lets = ref [] in

  let rewrite_view (pat, annot) =
    match pat with
    | P_app (view, [pat]) when not (Env.is_union_constructor view (env_of_annot annot)) ->
       let id = gen_view_id () in
       guards := view_guard annot view id pat :: !guards;
       lets := view_let annot view id pat :: !lets;
       P_aux (P_id id, annot)
    | _ -> P_aux (pat, annot)
  in

  let rewrite_pexp (Pat_aux (pexp_aux, pexp_annot)) =
    let pexp_aux = match pexp_aux with
      | Pat_exp (pat, exp) ->
         guards := [];
         let pat = fold_pat { id_pat_alg with p_aux = rewrite_view } pat in
         if List.length !guards > 0 then
           Pat_when (pat, List.hd !guards, List.hd !lets exp)
         else
           Pat_exp (pat, exp)
      | Pat_when (pat, guard, exp) -> Pat_when (pat, guard, exp)
    in
    Pat_aux (pexp_aux, pexp_annot)
  in

  let rewrite_case (exp, pexps) =
    E_case (exp, List.map rewrite_pexp pexps)
  in

  rewrite_defs_base {
      rewriters_base with
      rewrite_exp = (fun _ -> fold_exp { id_exp_alg with e_case = rewrite_case })
    }
