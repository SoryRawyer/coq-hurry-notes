Require Import Arith.
Require Import Bool.
(* Chapter 3 of "Coq in a hurry" — Propositions and Proofs *)

(* While t:B can say that value t is of type B, it also expresses that t is a proof
  for the logical formula B

  Similarly, the symbol "->", which before was used to represent function types,
  here represents implication between propositions

  Apparently the ambiguity of "->" rarely interferes in practice

  "SearchRewrite" is similar to "SearchPattern", but it only looks for rewriting theorems
  rewriting theorems are theorems where the proved predicate is an equality
  the theorems listed are those for which the pattern fits one side of the equality 
*)

(*
  Contructing proofs

  The usual approach to doing this is known as a "goal directed proof":
  1. the user enters a statement they'd like to prove, using the keyword "Theorem" or "Lemma" 
    along with a name for reference
  2. Coq displays the formula as a formula to be proved, possibly giving a context of local facts
    that can be used for the proof (the context is displayed above a horizontal line:
    =====
    and the goal is displayed below the line)
  3. the user enters a command to decompose the goal into simpler ones
  4. Coq displays the formulas that still need to be proved
  5. back to step 3

  The command at step 3 are called "tactics" and some actually decrease the number of goals
  The proof is complete when there are no more goals, at which point the user enters the command "Qed."
  "Qed" saves the proof to the name given in step one
*)

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.

(*
  1/1
  forall a b : Prop, a /\ b -> b /\ a
*)
Proof.
intros a b H.

(*
  a, b: Prop
  H: a /\ b
  ================
  1/1
  b /\ a
*)

split.
(*
  a, b: Prop
  H: a /\ b
  1/2
  b
  2/2
  a
*)

destruct H as [H1 H2].
(*
  a, b: Prop
  H1: a
  H2: b
  1/2
  b
  2/2
  a
*)

exact H2.
(*
  a, b: Prop
  H: a /\ b
  1/1
  a
*)

intuition.
(* No more subgoals. *)

Qed.
(* example2 is defined *)

(*
  We just defined and proved a theorem called example2
  The tactics we used were split, destruct, exact, and intuition (I think)

  Each goal has two parts: a context and a conclusion
  The elements of the context usually have two parts:
  - a : type
  - H : formula
  we call these "hypotheses", and we temporarily assume them to hold 

  "destruct" was used because the hypothesis H was a proof of a conjunction of two propositions.
  The effect of the tactic was to add two new hypotheses, H1 and H2, and remove H

  tactics can be conceptually the same, but have different keywords depending on whether they're
  used in a hypothesis of the context or in the conclusion of the goal

  the first step of the proof works on a universal quantification in the conclusion,
  so we use "intros", which has three arguments: a, b, and H. two universal quantifications and one implication

  The second step works on a conjunction and in the conclusion, so we use "split"

  The third step works on a conjunction and in the hypothesis H, so we use "destruct"

  the fourth step is not in the table below,


  +--------------+----------+----------------------------------------------+
  |              | implies  | for all            | conjunction             | 
  +--------------+----------+--------------------+-------------------------+
  | Hypothesis H | apply H  | apply H            | elim H                  |
  |              |          |                    | case H                  |
  |              |          |                    | destruct H as [H1 H2]   |
  +--------------+----------+--------------------+-------------------------+
  | conclusion   | intros H | intros H           | split                   |
  +--------------+----------+--------------------+-------------------------+
  
  +--------------+----------+----------------------------------------------+
  |              | not      | there exists       | disjunction (or)        | 
  +--------------+----------+--------------------+-------------------------+
  | Hypothesis H | elim H   | elim H             | elim H                  |
  |              | case H   | case H             | case H                  |
  |              |          |destruct H as [x H1]| destruct H as [H1 | H2] |
  +--------------+----------+--------------------+-------------------------+
  | conclusion   | intros H | exists H           | left or                 |
  |              |          |                    | right                   |
  +--------------+----------+--------------------+-------------------------+

  +--------------+----------+----------------------------------------------+
  |              | =        | False              |                         | 
  +--------------+----------+--------------------+-------------------------+
  | Hypothesis H | rewrite H| elim H             |                         |
  |              |(rewrite  | case H             |                         |
  |              |   <- H)  |                    |                         |
  |              |          |                    |                         |
  +--------------+----------+--------------------+-------------------------+
  | conclusion   | reflexi- |                    |                         |
  |              |-vity ring|                    |                         |
  +--------------+----------+--------------------+-------------------------+
*)
