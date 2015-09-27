(*  Title:      HOL/Hoare/hoare_tac.ML
    Author:     Leonor Prensa Nieto & Tobias Nipkow

Derivation of the proof rules and, most importantly, the VCG tactic.
*)








(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

(**Simp_tacs**)

fun before_set2pred_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps [Collect_conj_eq RS sym, @{thm Compl_Collect}]);

fun split_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]);

(*****************************************************************************)
(** set_to_pred_tac transforms sets inclusion into predicates implication,  **)
(** maintaining the original variable names.                                **)
(** Ex. "{x. x=0} <= {x. x <= 1}" -set2pred-> "x=0 --> x <= 1"              **)
(** Subgoals containing intersections (A Int B) or complement sets (-A)     **)
(** are first simplified by "before_set2pred_simp_tac", that returns only   **)
(** subgoals of the form "{x. P x} <= {x. Q x}", which are easily           **)
(** transformed.                                                            **)
(** This transformation may solve very easy subgoals due to a ligth         **)
(** simplification done by (split_all_tac)                                  **)
(*****************************************************************************)

fun set_to_pred_tac ctxt var_names = SUBGOAL (fn (_, i) =>
  before_set2pred_simp_tac ctxt i THEN_MAYBE
  EVERY [
    rtac subsetI i,
    rtac CollectI i,
    dtac CollectD i,
    TRY (split_all_tac ctxt i) THEN_MAYBE
     (rename_tac var_names i THEN
      full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]) i)]);

(*******************************************************************************)
(** basic_simp_tac is called to simplify all verification conditions. It does **)
(** a light simplification by applying "mem_Collect_eq", then it calls        **)
(** max_simp_tac, which solves subgoals of the form "A <= A",                 **)
(** and transforms any other into predicates, applying then                   **)
(** the tactic chosen by the user, which may solve the subgoal completely.    **)
(*******************************************************************************)

fun max_simp_tac ctxt var_names tac =
  FIRST' [rtac subset_refl, set_to_pred_tac ctxt var_names THEN_MAYBE' tac];

fun basic_simp_tac ctxt var_names tac =
  simp_tac
    (put_simpset HOL_basic_ss ctxt
      addsimps [mem_Collect_eq, @{thm split_conv}] addsimprocs [Record.simproc])
  THEN_MAYBE' max_simp_tac ctxt var_names tac;



(** hoare_rule_tac **)

fun hoare_rule_tac ctxt tac =
  let
 
    fun wlp_tac i =
      stac @{thm SeqRule} i
   
     and rule_tac pre_cond i st = st |> (*abstraction over st prevents looping*)
      (
          stac @{thm validdef} 1 THEN rule_tac pre_cond i  ORELSE
         ( (wlp_tac i THEN rule_tac pre_cond i)
              ORELSE
               (  stac @{thm SkipRule} 1 THEN rule_tac pre_cond i 
                    ORELSE( stac @{thm InitRule} 1 THEN rule_tac pre_cond i 
                      ORELSE ( stac @{thm UtransRule} 1 THEN rule_tac pre_cond i 
                      ORELSE ( stac @{thm MeasureRule} 1 THEN rule_tac pre_cond i
                      ORELSE ( stac @{thm WhileRule} 1 THEN rule_tac pre_cond i
                      ORELSE (K all_tac 1)
 )
 )
 )                  
 )
    )
        ) );
  in rule_tac end;


(** tac is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                       **)

fun quantum_hoare_tac ctxt tac = SUBGOAL (fn (goal, i) =>
  SELECT_GOAL (hoare_rule_tac ctxt  tac true 1) i);

