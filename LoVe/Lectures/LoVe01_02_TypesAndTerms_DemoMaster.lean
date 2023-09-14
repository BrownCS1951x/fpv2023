/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- 

# FPV Lecture 1: Types, Terms, Definitions (Ch. 1-2)

We start our journey by studying the basics of Lean, starting with terms
(expressions) and their types. -/


namespace LoVe


/- ## A View of Lean

In a first approximation:

    Lean = functional programming + logic

In today's lecture, we cover the syntax of types and terms, which are similar to
those of the simply typed λ-calculus or typed functional programming languages
(ML, OCaml, Haskell).


## Types

Types `σ`, `τ`, `υ`:

* type variables `α`;
* basic types `T`;
* complex types `T σ1 … σN`.

Some type constructors `T` are written infix, e.g., `→` (function type).

The function arrow is right-associative:
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`.

Polymorphic types are also possible. In Lean, the type variables must be bound
using `∀`, e.g., `∀α, α → α`.


## Terms

Terms `t`, `u`:

* constants `c`;
* variables `x`;
* applications `t u`;
* anonymous functions `fun x ↦ t` (also called λ-expressions).

__Currying__: functions can be

* fully applied (e.g., `f x y z` if `f` can take at most 3 arguments);
* partially applied (e.g., `f x y`, `f x`);
* left unapplied (e.g., `f`).

Application is left-associative: `f x y z` = `((f x) y) z`.

`#check` reports the type of its argument. -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` defines an arbitrary constant of the specified type. -/


opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## Type Checking and Type Inference

Type checking and type inference are decidable problems (although this property is
quickly lost if features such as overloading or subtyping are added).

Type judgment: `C ⊢ t : σ`, meaning `t` has type `σ` in local context `C`.

Typing rules:

    —————————— Cst   if c is globally declared with type σ
    C ⊢ c : σ

    —————————— Var   if x : σ is the rightmost occurrence of x in C
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

If the same variable `x` occurs multiple times in the context C, the rightmost
occurrence shadows the other ones.


## Type Inhabitation

Given a type `σ`, the __type inhabitation__ problem consists of finding a term
of that type. Type inhabitation is undecidable.

Recursive procedure:

1. If `σ` is of the form `τ → υ`, a candidate inhabitant is an anonymous
   function of the form `fun x ↦ _`.

2. Alternatively, you can use any constant or variable `x : τ₁ → ⋯ → τN → σ` to
   build the term `x _ … _`. -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))







/- ## Type Definitions

An __inductive type__ (also called __inductive datatype__,
__algebraic datatype__, or just __datatype__) is a type that consists all the
values that can be built using a finite number of applications of its
__constructors__, and only those.


### Natural Numbers -/

namespace MyNat

/- Definition of type `Nat` (= `ℕ`) of natural numbers, using unary notation: -/


inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat


#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` outputs the definition of its argument. -/

#print Nat

end MyNat

/- Outside namespace `MyNat`, `Nat` refers to the type defined in the Lean core
library unless it is qualified by the `MyNat` namespace. -/

#print Nat
#print MyNat.Nat




/- ### Arithmetic Expressions -/


inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp



/- ### Lists -/

namespace MyList


inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α


#check List

#check List.nil
#check List.cons

#print List

end MyList

#print List
#print MyList.List


/- ## Function Definitions

The syntax for defining a function operating on an inductive type is very
compact: We define a single function and use __pattern matching__ to extract the
arguments to the constructors. -/


def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n


/- When there are multiple arguments, separate the patterns by `,`: -/


def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)


/- `#eval` and `#reduce` evaluate and output the value of a term. -/


#eval add 2 7
#reduce add 2 7



def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)



#eval mul 2 7


#print mul


def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)


#eval power 2 5

/- `add`, `mul`, and `power` are artificial examples. These operations are
already available in Lean as `+`, `*`, and `^`.

If it is not necessary to pattern-match on an argument, it can be moved to
the left of the `:` and made a named argument: -/


def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)


#eval powerParam 2 5


def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)


#check iter


def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n


#eval powerIter 2 5


def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]



def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂



#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))


/- Lean only accepts the function definitions for which it can prove
termination. In particular, it accepts __structurally recursive__ functions,
which peel off exactly one constructor at a time.


## Theorem Statements

Notice the similarity with `def` commands. `theorem` is like `def` except that
the result is a proposition rather than data or a function. -/

namespace SorryTheorems


theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
  sorry



theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  sorry



theorem reverse_reverse {α : Type} (xs : List α) :
  reverse (reverse xs) = xs :=
  sorry


/- Axioms are like theorems but without proofs. Opaque declarations are like
definitions but without bodies. -/


opaque a : ℤ
opaque b : ℤ



axiom a_less_b :
  a < b


end SorryTheorems




/- 

## A preview of Ch. 4 


We just defined "basic" types like `ℕ`, and "compound"
types like `list ℕ` and `ℕ → ℕ`.

We even saw hints of "type parametricity," like for `id`:
(Note: read `Sort` as `Type`.)
-/

def eid (α : Type) (a : α) : α := a
#check eid


/-
But in general, every *term* has a *type* associated with it.
Terms are on the left of the `:` and types are on the right.
There was some weirdness here when we wrote `#check Type` and the answer
was `Type 1`...



Consider a function `pick` that take a number `n : ℕ` and that returns a number
between 0 and `n`. Conceptually, `pick` has a dependent type, namely

    `(n : ℕ) → {i : ℕ // i ≤ n}`

We can think of this type as a `ℕ`-indexed family, where each member's type may
depend on the index:

    `pick n : {i : ℕ // i ≤ n}`

This is a *type* that contains, or depends on, a (non-Type) *term*.

-/

#check Fin 10 
#check (2 : Fin 10)

#check (n : ℕ) → {i : ℕ // i ≤ n}


/- Example of a term that depends on a term: -/


/- Example of a term that depends on a type: -/


/- Example of a type that depends on a type: -/




/-

Unless otherwise specified, a __dependent type__ means a type depending on a
term. This is what we mean when we say that simple type theory does not support
dependent types.

In summary, there are four cases for `fun x ↦ t` in the calculus of inductive
constructions (cf. Barendregt's `λ`-cube):

Body (`t`) |              | Argument (`x`) | Description
---------- | ------------ | -------------- | ----------------------------------
A term     | depending on | a term         | Simply typed anonymous function
A type     | depending on | a term         | Dependent type (strictly speaking)
A term     | depending on | a type         | Polymorphic term
A type     | depending on | a type         | Type constructor





-/

end LoVe
