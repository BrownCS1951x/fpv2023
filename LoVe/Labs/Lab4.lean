import LoVe.Lectures.LoVe04_ForwardProofs_Demo


/- # FPV Lab 4: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

theorem reverseAccu_Eq_reverse_append {α : Type} :
  ∀ as xs : List α, reverseAccu as xs = reverse xs ++ as
:=   sorry

/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
  reverseAccu [] xs = reverse xs :=
  sorry

/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
  reverseAccu [] (reverseAccu [] xs) = xs :=
  sorry


/- ## Question 2: Vectors and Matrices

Recall the type constructor `Vec : Type → Nat → Type` that represents a sequence
of values of a particular length. -/

inductive Vec (α : Type) : Nat → Type
  | nil                                  : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)

-- The section below defines notation for vectors. You do not need to understand
-- this code; we recommend "collapsing" it by clicking the arrow that appears
-- when hovering to the left of `section`.
section
syntax "V[" withoutPosition(term,*) "]"  : term
macro_rules
  | `(V[ $[$elems],* ]) => do
      elems.foldrM (β := Lean.Term) (init := (← `(Vec.nil))) λ x k =>
        `(Vec.cons $x $k)

def joinSepV {α : Type} [Std.ToFormat α] {n : Nat}
    : Vec α n → Std.Format → Std.Format
  | V[],    _   => .nil
  | V[a],   _   => Std.format a
  | Vec.cons a as, sep => Std.format a ++ sep ++ joinSepV as sep
instance {α} [Repr α] {n : Nat} : Repr (Vec α n) := ⟨λ
  | V[], _ => "V[]"
  | as, _ =>
    let _ : Std.ToFormat α := ⟨repr⟩
    Std.Format.bracket "V[" (joinSepV as ("," ++ Std.Format.line)) "]"
⟩

@[app_unexpander Vec.nil] def unexpandVecNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(V[])
@[app_unexpander Vec.cons] def unexpandVecCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x V[])      => `(V[$x])
  | `($(_) $x V[$xs,*]) => `(V[$x, $xs,*])
  | _                  => throw ()
end

-- Here are some sample vectors using both explicit and shorthand notations:
#eval (Vec.nil : Vec String 0)
#eval (V[] : Vec Bool 0)
#eval (Vec.cons "hello" (Vec.cons "world" Vec.nil) : Vec String 2)
#eval (V[1, 9, 5, 1] : Vec Nat 4)

namespace Vec

/- We can define functions on vectors just as we do on lists and trees. For
instance, here's an `append` function on vectors analogous to its counterpart
for lists: -/

def append {α : Type} {m n : Nat} : Vec α m → Vec α n → Vec α (n + m)
  | Vec.nil      , ys => ys
  | Vec.cons x xs, ys => Vec.cons x (append xs ys)

#check append V[3, 1] V[4, 1, 5]
#eval append V[3, 1] V[4, 1, 5]

/- 2.1. Implement the function `dotProduct` that computes the dot product of two
equal-dimensional (i.e., equal-length in the programmatic sense) vectors with
integer coordinates (i.e., elements). The dot product of two vectors
`V[v₁, v₂, ..., vₙ]` and `V[w₁, w₂, ..., wₙ]` is the number
`v₁ * w₁ + v₂ * w₂ + ... + vₙ * wₙ`, or, more formally, `∑_{i=1}^n (vᵢ * wᵢ)`. -/

def dotProduct {n : Nat} : Vec Nat n → Vec Nat n → Nat
  := sorry

/- 2.2. We define the *melding* (a coined term) of two equal-length vectors to
be the vector formed by applying a combining function to each corresponding pair
of elements in the two vectors. For instance, the melding of `V[1, 2, 3]` and
`V[4, 5, 6]` using the combining function `(·+·)` would be the vector
`V[5, 7, 9]`.

Implement a function `meld` that performs this operation. (You'll need to fill
in both the type and body of the function.) Ensure that the type of `meld` is as
general as possible. -/

def meld : sorry := sorry

/- The *product* of two types `α` and `β`, denoted `α × β`, is the type of
pairs `(a, b)` such that `a : α` and `b : β`. (`(a, b)` is syntactic sugar for
`Prod.mk a b`, where `Prod.mk : ∀ {α β : Type}, α → β → α × β`.) -/

#check (1, 2)
#check Prod.mk 1951 "X"

/- 2.3. The *zipping* of two vectors is the vector formed by pairing
corresponding elements. For instance, zipping `V[1, 2, 3] : Vec Nat 3` and
`["a", "b", "c"] : Vec String 3` yields the vector
`[(1, "a"), (2, "b"), (3, "c")] : Vec (Nat × String) 3`.

Use `meld` to implement `zip`. The only modification you may make to the line
below is to replace `sorry` with a *non-recursive* function. -/

def zip {α β : Type} {n : Nat} : Vec α n → Vec β n → Vec (α × β) n :=
  meld sorry

/- 2.4. Prove the lemma below that says that appending and melding can be done
in either order -- that is, that melding the results of appending two pairs of
vectors is the same as appending the result of melding two pairs of vectors.

You may prove your base case however you wish. However, for the inductive
case, you must use `calc` mode, and you may only use the following terms in your
proof (i.e., as "justifications" after the `:=` in `calc` mode):
* `rfl`
* `by rw [ih]`

(In practice, this means that you need to "step" your code as you would in a
pen-and-paper proof; you can't use `simp` to bypass reasoning steps.)

You will also need to fill in the `ih` declaration with the appropriate
variables. -/

theorem meld_append {α β γ : Type} {m n : Nat} (f : α → β → γ) :
  ∀ (vs : Vec α n) (ws : Vec β n) (xs : Vec α m) (ys : Vec β m),
    meld f (append vs xs) (append ws ys) =
    append (meld f vs ws) (meld f xs ys)
  | Vec.nil, Vec.nil, xs, ys =>
    sorry
  | Vec.cons v vs, Vec.cons w ws, xs, ys =>
    have ih := meld_append sorry sorry sorry sorry sorry
    sorry

end Vec

/- 2.5. Having defined vectors, we now turn our attention to matrices. An
`r`-by-`c` matrix is a "grid" of numerical entries (we'll use the naturals to
make things simple) with `r` rows and `c` columns. We can think of them as
vectors of vectors: either a length-`c` vector of `r`-element column vectors, or
a length-`r` vector of `c`-element row vectors.

For this problem, we'll use the *row-wise* representation: that is, we'll think
of matrices as a vector containing row vectors.

Fill in the type-level function that defines this type below. That is, `Mat r c`
should evaluate to the type whose values are row-wise representations of
matrices that store natural numbers as their entries. -/

def Mat (r : Nat) (c : Nat) : Type :=
  sorry

-- The errors below should disappear if you've defined the type correctly!
#eval (V[] : Mat 0 0)
#eval (V[V[11, 12], V[21, 22], V[31, 32]] : Mat 3 2)
#eval (V[V[1, 3, 4], V[2, 2, 5]] : Mat 2 3)

/- 2.6. The first kind of matrix operation we'll implement is extracting
subcomponents. Below, implement the functions `getRow` and `getCol` that,
respectively, extract a row or column at a specified index from a matrix.

Notice an interesting feature of these functions: they each take as an argument
a *proof* that the requested row or column index is legal for the given matrix.
This allows us to enforce the legality of arguments at the type level.

We provide two helper functions below that you will likely find helpful. (Hint:
notice the second explicit argument to `Vec.nth`!) -/

def Vec.map {α β : Type} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | Vec.nil       => Vec.nil
  | Vec.cons x xs => Vec.cons (f x) (Vec.map f xs)

def Vec.nth {α : Type} {n : Nat} : ∀ (i : Nat), i < n → Vec α n → α
  | 0    , h, Vec.cons x _  => x
  | n + 1, h, Vec.cons x xs => Vec.nth n (Nat.lt_of_succ_lt_succ h) xs

namespace Mat

def getRow {r c : Nat} (i : Nat) (h : i < r) (m : Mat r c) : Vec Nat c :=
  sorry

def getCol {r c : Nat} (i : Nat) (h : i < c) (m : Mat r c) : Vec Nat r :=
  sorry

/- 2.7. Our second matrix operation is addition. Matrix addition proceeds
component-wise: e.g.,
┌     ┐   ┌     ┐     ┌         ┐
| a b | + | e f |  =  | a+e b+f |
| c d |   | g h |     | c+g d+h |
└     ┘   └     ┘     └         ┘

Below, implement a function `add` for adding two matrices.

Hint: You're free to use any of the vector helper functions we've defined,
including `Vec.meld`, `Vec.zip`, and `Vec.map`. There are many solutions; see if
you can find one that is particularly concise and expressive. -/

def add {r c : Nat} : Mat r c → Mat r c → Mat r c :=
  sorry

end Mat


/- ## Question 3: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 3.1. Define the `take` function, which returns a list consisting of the the
first `n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → List α → List α
:=   sorry

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 3.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : List α) = []
:=   sorry

@[simp] theorem take_nil {α : Type} :
  ∀n : ℕ, take n ([] : List α) = []
:=   sorry

/- 3.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

theorem drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,     n, xs      => by rfl
  -- supply the two missing cases here

theorem take_take {α : Type} :
  ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
:=   sorry

theorem take_drop {α : Type} :
  ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs
:=   sorry


/- ## Question 4: A Type of Terms

4.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

-- enter your definition here

/- 4.2. Register a textual representation of the type `term` as an instance of
the `Repr` type class. Make sure to supply enough parentheses to guarantee that
the output is unambiguous. -/

def Term.repr : Term → String
-- enter your answer here

instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 4.3. Test your textual representation. The following command should print
something like `(λx. ((y x) x))`. -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
