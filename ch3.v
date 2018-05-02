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

(* 3.3.1 — examples using "apply" *)

(*
  apply is adapted especially to work on hypotheses or theorems whose main connective is a universal
  quantification or implication. It works by separating the conclusion of a theorem from its premeses,
  by matching the conclusion of the theorem with the conclusion of the current goal to guess
  as many universally quantified

  Basically, I think that apply will break up a theorem statement like
  "A1 x1...xK -> A2 x1...xK -> ... -> AN x1...xK"
  into N number of goals:
  "A1 a1...aK, A2 a1...aK, ..., AN a1...aK"
  this way, Coq can infer that a1 is supposed to be x1, etc.
  If a variable doesn't appear in the theorem's conclusion, Coq won't be able to infer it's value
  but users can still specify it using "with"
*)

Check le_S.
(* le_S
     : forall n m : nat, n <= m -> n <= S m *)
Check le_n.
(* le_n
     : forall n : nat, n <= n *)

Lemma example4: 3 <= 5.
(*
  keeping in mind that 3 is actually S (S (S 0)) and 5 is S (S (S (S (S 0)))),
  we can apply le_S to our goal, until we get to the point where
  we can apply le_n

  applying le_S will match 3 <= 5 with n <= m, translate that to n <= S m,
  and then replace 5 with 4 to give us 3 <= 4, matching the format of our premise

  I'm not sure how it knows to do a transformation vs prove our goal
*)
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.
(* example4 is defined *)

(*
  basically, I think we're just pushing symbols around to see if we can match
  parts of our proofs to theorems
*)

(*
  below is an example of a theorem where some variable that is universally quantified in the hypothesis
  or theorem statement is not present in the theorem's conclusion
  common theorems with this trait are transitivity theorems
*)

Check le_trans.
(* Nat.le_trans
     : forall n m p : nat, n <= m -> m <= p -> n <= p *)

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
  intros x y x10 y10.
  (*
    x, y: nat
    x10: x <= 10
    y10: 10 <= y
    ============
    1/1
    x <= y

    here, we're introducing the variables x and y, as well as the hypotheses
    x10 and y10, which stand for x <=10 and 10 <= y, respectively
  *)

  (*
    apply le_trans.
    Unable to find an instance for the variable m.

    Since there's no variable that fills m's role, only the constant 10,
    then we need to specify m
  *)
  apply le_trans with (m := 10).
  (*
    x, y: nat
    x10: x <= 10
    y10: 10 <= y
    =============
    1/2
    x <= 10
    2/2
    10 <= y
  *)
  assumption.
  (*
    x, y: nat
    x10: x <= 10
    y10: 10 <= y
    ============
    1/1
    10 <= y

    since our hypothesis x10 matches the first subgoal goal exactly, we can
    just call "assumption" and call it a day
  *)

  assumption.
  (* ditto y10 and subgoal 2 *)
Qed.
(* example5 is defined *)

(* 3.3.2 — examples using "rewrite" *)

(*
  Many theorems have a conclusion which is an equality.
  To use these, we can use the "rewrite" tactic
  "rewrite", by default, will try to find patterns in the left hand side of a theorems conclusion
  This can be reversed by saying "rewrite <-"
*)

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
  intros x y.
  (*
    x, y: nat
    ================
    1/1
    (x + y) * (x + y) = x * x + 2 * x * y + y * y
  *)

  (*
    "SearchRewrite" will look for theorems where only one side of the equality
    matches the pattern searched for.
  *)
  SearchRewrite (_ * (_ + _)).
  (* Nat.mul_add_distr_l: forall n m p : nat, n * (m + p) = n * m + n * p *)
  rewrite Nat.mul_add_distr_l.
  (*
    x, y: nat
    =============
    1/1
    (x + y) * x + (x + y) * y = x * x + 2 * x * y + y * y

    here, we can see that Coq automatically discovered the following mapping:
    n : (x + y)
    m : x (from the second (x + y) term)
    p : y (from the second (x + y) term)
  *)
  SearchRewrite ((_ + _) * _).
  (* Nat.mul_add_distr_r: forall n m p : nat, (n + m) * p = n * p + m * p *)
  rewrite Nat.mul_add_distr_r.
  (*
    x, y: nat
    ==============
    1/1
    x * x + y * x + (x + y) * y = x * x + 2 * x * y + y * y

    run it again to fully expand the thing
  *)
  rewrite Nat.mul_add_distr_r.
  (*
    x, y: nat
    ==============
    1/1
    x * x + y * x + (x * y + y * y) = x * x + 2 * x * y + y * y
  *)
  SearchRewrite (_ + (_ + _)).
  (*
    vscoq apparently doesn't want to show more than 1 search result
    this is what we want:
    Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
  *)
  rewrite Nat.add_assoc.
  (*
    x, y: nat
    =================
    1/1
    x * x + y * x + x * y + y * y = x * x + 2 * x * y + y * y
  *)
  rewrite <- Nat.add_assoc with (n := x * x).
  (*
    without "with", the rewrite would've chosen the following:
    n: y * x
    m: x * y
    p: y * y

    the "<-" here means that we want to match our goal to the right side of Nat.add_assoc,
    then rewrite the goal so that it looks like the left side of Nat.add_assoc
  *)
  SearchPattern (?x * ?y = ?y * ?x).
  (* Nat.mul_comm: forall n m : nat, n * m = m * n *)

  rewrite Nat.mul_comm with (n := y) (m := x).
  (*
    x, y: nat
    =============
    1/1
    x * x + (x * y + x * y) + y * y = x * x + 2 * x * y + y * y
  *)

  (*
    now, we just need to combine the two x*y terms in the middle
    2 is really just S (S 0), so let's *search* for *rewrite patterns* like that
  *)
  SearchRewrite (S _ + _).
  (*
    the ones we want are:
    Nat.mul_1_l: forall n : nat, 1 * n = n
    Nat.mul_succ_l: forall n m : nat, S n * m = n * m + m
  *)
  rewrite <- (Nat.mul_1_l (x * y)) at 1.
  (*
    x, y: nat
    =============
    1/1
    x * x + (1 * (x * y) + x * y) + y * y = x * x + 2 * x * y + y * y

    we say "at 1" here to make sure that this rule is only applied once
  *)

  rewrite <- Nat.mul_succ_l.
  (*
    x, y: nat
    =============
    1/1
    x * x + 2 * (x * y) + y * y = x * x + 2 * x * y + y * y

    so close. we just need to lose the parens. to the rewrite-searcher!
  *)

  SearchRewrite (_ * (_ * _)).
  (* Nat.mul_assoc: forall n m p : nat, n * (m * p) = n * m * p *)

  rewrite Nat.mul_assoc.
  (*
    x, y: nat
    =============
    1/1
    x * x + 2 * x * y + y * y = x * x + 2 * x * y + y * y

    finally
  *)

  reflexivity.
Qed.
(* example6 is defined *)


(* 3.3.3 — examples using "unfold" *)

(*
  sometimes we just wanna replace an expression with another expression
  that is the same by definition, just by ~*unfolding*~ definitions
  as an example, we are going to prove sum'n about "Nat.pred"
*)

Print Nat.pred.
(*
  Nat.pred = 
  fun n : nat => match n with
                 | 0 => n
                 | S u => u
                 end
       : nat -> nat
*)

Lemma pred_S_eq : forall x y, x = S y -> Nat.pred x = y.
Proof.
  intros x y q.
  (*
    x, y: nat
    q: x = S y
    ===============
    1/1
    Nat.pred x = y
  *)

  unfold Nat.pred.
  (*
    x, y: nat
    q: x = S y
    ==============
    1/1
    match x with
    | 0 => x
    | S u => u
    end = y

    here, Coq will allow us to kind of use the definition of Nat.pred to pattern match against q
  *)

  rewrite q.
  (*
    x, y: nat
    q: x = S y
    ==========
    1/1
    y = y

    since q represented x = S y, it was matched against the second case of Nat.pred, and y was returned    
  *)

  reflexivity.
  (* No more subgoals. *)
Qed.
(* pred_S_eq is defined *)

(* 3.4 — more advanced tactics *)

(*
  "intuition" and "tauto" are useful to prove facts that are tautologies in propositional logic
  try it whenever the proof only involves manipulations of conjunction, disjunction, and negation,
  like in example 2, which could've been solved with one call to "intuition"

  "firstorder" can be used for tautologies in first-order logic
  try it whenever the proof only involves the same connectives as tauto, plus existential and 
  universal qunatifications

  "auto" is an extensible tactic that tries to apply a collection of theorems that were provided
  beforehand by the user
  "eauto" is like "auto", but is more powerful and takes longer to run

  "ring" mostly does proofs of equality for expressions containing addition and multiplication

  "omega" proves systems of linear equations
  an equation is linear when it is of the form:
  A <= B, or A < B, and A and B are sums of terms of the form n*x, where x is a variable and n in a constant
  it can also be used for problems which are instances of linear inequations
  below is an example where f x is not a linear term, but the whole system of equations is 
  the instance of a linear system.
*)

Require Import Omega.

Lemma omega_example : 
forall f x y, 0 < x -> 0 < f x -> 3 * f x <= 2 * y -> f x <= y.
Proof.
  intros.
  (*
    f: nat -> nat
    x, y: nat
    H: 0 < x
    H0: 0 < f x
    H1: 3 * f x <= 2 * y
    1/1
    =====================
    f x <= y
  *)
  omega.
  (* no more subgoals *)
Qed.
(* omega_example is defined *)

