(*
    Check will tell you if a formula is well-formed
    kind of like a syntax checker I guess?
 *)
(* 
    Commands are always terminated by a period
 *)
Check False.
Check 3.
Check (3 + 4).
Check (3=5).
(* 3 = 5 : Prop *)
Check nat -> Prop. 
(* nat -> Prop. : Type *)

(* 
    Some of the above formulas are:
        - natural numbers (type nat) (e.g. — 3 and 4)
        - logical propositions (type Prop) (e.g. — 3 = 5)
        - types (e.g. — nat -> Prop)
*)

Check (fun x:nat => x = 3).
(*
    fun x : nat => x = 3
    : nat -> prop
    takes a natural number, x, and returns the proposition that x is less than 3
*)

Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
(* 
    forall x : nat, x < 3 \/ (exists y : nat, x = y + 3)
     : Prop
*)

(* let .. in makes it possible to give a temporary name to an expression *)

Check (let f := fun x => (x * 3, x) in f 3).

(*
    in the example above, the function f takes a number and returns a pair of numbers
*)

(*
    Some functions are *overloaded*, like "*", which is used to represent both multiplication and the cartesian product on types
*)

(*
    We can find the function behind a notation by using "Locate", shown below
*)

Locate "_ <= _".

(*
    Notation
    "n <= m" := le n m : nat_scope (default interpretation)
*)

(*
    For a term to be well-formed, there are two criteria:
    - syntax must be respected (balanced parens, period at the end, etc)
    - expressions must respect a type discipline
*)

(*
    Function applications seem to be curried by default. e.g. — a -> b -> c really represents a -> (b -> c)

    function "and" has a type of Prop -> Prop -> Prop, so when we execute (and True False)., what we're really doing is applying the result of (and True) to False (the parents for and True are used for clarity. In Coq syntax they would not be used)
*)

(*
    Coq evaluates expressions using the Compute keyword
*)

Compute let f := fun x => (x * 3, x) in f 3.

(*
    = (9, 3)
    : nat * nat
    (remember, * also means cartesian product)
*)

(*
    exercise on functions:
    wite a function that takes 5 arguments and returns their sum
*)

Check (let f := fun x y z a b => (x + y + z + a + b) in f 1 2 3 4 5).

Compute (let f := fun x y z a b => (x + y + z + a + b) in f 1 2 3 4 5).

(* :thumbsup: *)
