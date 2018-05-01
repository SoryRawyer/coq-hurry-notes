(* chapter 2 of "coq in a hurry" *)

(* Constants are defined with the Definition keyword *)

Definition example1anon := fun x : nat => x*x+2*x+1.

(* alternative definition, without an anonymous function: *)

Definition example1 (x : nat) := x * x+2 * x+1.

Check example1anon.
Check example1.
(* nat -> nat *)

Compute example1 1.
(* = 4 : nat *)

(* the "Reset" command will force Coq to forget a definition you just made *)

(* Reset example1. *)

(* I'm assuming this is more useful in an interpreter, rather than executing lines in a file *)

(* "Print" will show you the definition of a command *)

Print example1.

(*
  example1 = fun x : nat => x * x + 2 * x + 1
     : nat -> nat

  Argument scope is [nat_scope]
*)

(* booleans are "true" and "false" *)

Require Import Bool.

Compute if true then 3 else 5.

(* = 3 : nat *)

SearchPattern bool.

(*
  "SearchPattern" takes a pattern and returns any symbol whose type finishes with that pattern
  "Search" takes a list of patterns and returns any symbol whose type contains all the patterns in the list

  kind of like a regex search on function signatures
*)


Require Import Arith.

(*
  For natural numbers, we can think of each number as satisfying one of two properties:
  - it is 0
  - it is a successor of some natural number P

  For example, see the is_zero function below, which uses pattern matching to identify if a number is zero or not:
*)

Definition is_zero (n:nat) :=
  match n with
    0 => true
    | S p => false
  end.


(* Recursive functions need to be declared using the keyword "Fixpoint" *)

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Compute sum_n 4.
(*  = 6 : nat *)

(*
  Coq will check that the recursive call to a function occurs on a subterm of the initial argument

  Calling sum_n on (S p) would have thrown an error, instead of running forever
*)

(* We can also use ~deep~ pattern matching: *)

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Compute evenb 6. (* true *)
Compute evenb 7. (* false *)

(* Lists *)

Require Import List.

Check 1::2::3::nil. (* : list nat *)

(* list concatenation: ++ or app *)

Check 1::2::nil ++ 3::nil.
Compute 1::2::nil ++ 3::nil. (* 1::2::3::nil : list nat *)

(* map does what you'd expect *)

Compute map (fun x => x + 3) (1::2::3::nil). (* 4::5::6::nil *)
Compute map S (1::22::3::nil). (* 2::23::4::nil *)

Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.
(* 1::2::3::4::5::6::nil *)

(* "Search" can give us all known theorems (in scope) that mention a given symbol *)
Search Nat.eqb.

Locate "_ =? _".
(* "x =? y" := Nat.eqb x y : nat_scope (default interpretation) *)

(* exercise: write a function that takes an input n and returns a list with elements 0 through n - 1 *)

Fixpoint list_n n :=
  match n with
    0 => nil
  | S p => p :: list_n p
  end.

Compute list_n 4.

(* Gah! it's backwards. turns out the solution was this: *)
Fixpoint list_n_aux (n:nat)(m:nat) :=
  match n with
    0 => nil
  | S p => m :: list_n_aux p (m+1)
  end.

Definition list_n_solution n := list_n_aux n 0.

Compute list_n_solution 4.

(*
  Exercise on sorting: write two functions:
  - return true if:
    - list length < 2
    - given a :: b :: tail, a < b
  - return true if input list is sorted
*)

Fixpoint first_two_ordered list :=
  match list with
    nil => true
  | head :: nil => true
  | frst :: scnd :: tail => frst <? scnd
  end.

Compute first_two_ordered (1::2::nil).
Compute first_two_ordered (2::nil).
Compute first_two_ordered (3::2::nil).

Search andb.

Fixpoint is_sorted list :=
  match list with
    nil => true
  | head :: nil => true
  | frst :: tail => andb (first_two_ordered list) (is_sorted tail)
  end.


Compute is_sorted (1::2::3::nil).
Compute is_sorted (1::2::3::1::nil).
Compute is_sorted (1::2::nil).
Compute is_sorted (1::nil).


(* Example: count occurrences of element in list *)
Fixpoint count list n :=
  match list with
    nil => 0
  | head :: tail => (if (head =? n) then 1 else 0) + (count tail n)
  end.

Compute count (1::2::3::nil) 1.
Compute count (1::2::3::1::3::4::nil) 3.

