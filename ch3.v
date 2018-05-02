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
  ================
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
  ================
  1/2
  b
  2/2
  a
*)

exact H2.
(*
  a, b: Prop
  H: a /\ b
  =================
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
  |              |-vity     |                    |                         |
  |              |   ring   |                    |                         |
  +--------------+----------+--------------------+-------------------------+

  "elim" and "case" may create new facts that are placed in the conclusion of resulting goals
  as premises of newly created implications
  these premises then need to be introduced in the context using "intros" ("intros" is used to work on
  implications when they're in the conclusion)
  the tactic "destruct" does these two operations at once

  tactics that work on hypotheses and take hypotheses names as arguments can also take theorem names as arguments

  Taken from https://coq.inria.fr/tutorial-nahas:
  RULE: If the subgoal starts with "(forall <name> : <type>, ..." Then use tactic "intros <name>."
*)

Lemma example3: forall A B, A \/ B -> B \/ A.
(* for any two propositions A and B, if A \/ B holds, then B \/ A holds *)
(* our first reasoning step introduces the universally quantified propositions and the hypothesis in the context *)
Proof.
  intros A B H.
  (*
    A, B: Prop
    H: A \/ B
    ============
    1/1
    B \/ A
  *)

  (*
    In English, this kinda means "let's fix two propositions, A and B, and let's assume A \/ B holds,
    now we only have to prove B \/ A"
    Since we can't really say anything about A and B (either one could be responsible for satisfying A \/ B),
    we should work on the hypothesis

    if A \/ B holds, then we have two cases: either A holds or B holds
    to get these two cases independently, we can run "destruct"
  *)

  destruct H as [H1 | H1].
  (*
    A, B: Prop
    H1: A
    ============
    1/2
    B \/ A
    2/2
    B \/ A

    Here, we see that we're working on a goal where H1 represents the case where A holds
    we can work directly on the conclusion and prove the right hand side: A
  *)

  right; assumption.

  (*
    A, B: Prop
    H1: B
    ===========
    1/1
    B \/ A

    "assumption" is getting applied to all the goals produced by "right"
    "right" transforms the goal's conclusion to "A"
    "assumption" then proves this by looking for assumptions with A as a statement. In this case, that's H1

    We see now that, having proved our first subgoal, we can move on to our second, the case where B holds
    We can follow the same procedure, but proving the left-hand side now
  *)

  left; assumption.
  (* no more subgoals *)
Qed.
(* example3 is defined *)