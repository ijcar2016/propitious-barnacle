(*  Title:      HOL/Hoare/hoare_tac.ML

Derivation of the proof rules and, most importantly, the VCG tactic.
*)








(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

(**Simp_tacs**)




(** hoare_rule_tac **)
(** hoare_rule_tac **)

fun hoare_rule_tac ctxt tac =
  let
     fun rule_tac pre_cond i st = st |>
      (
          rtac @{thm  ord_wlp} 1
    )
         
  in rule_tac end;


(** tac is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                       **)

fun quantum_hoare_tac ctxt tac = SUBGOAL (fn (goal, i) =>
  SELECT_GOAL (hoare_rule_tac ctxt  tac true 1) i);

