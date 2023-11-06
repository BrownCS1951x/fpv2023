import AutograderLib
import LoVe.LoVelib

/- # FPV Homework 8: Logical Foundations of Mathematics

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


namespace LoVe


/- ## Question 1 (9 points): Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `List α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `List.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `BEq` (Boolean equality) type class. For this reason, the definitions and
theorems below all take `[BEq α]` as type class argument.

1.1 (2 points). Provide the missing proof below. -/

instance Multiset.Setoid (α : Type) [BEq α] : Setoid (List α) :=
{ r     := fun as bs ↦ ∀x, List.count x as = List.count x bs
  iseqv :=
    { refl  :=
        sorry
      symm  :=
        sorry
      trans :=
        sorry
    } }

/- We can now define the type of multisets as the quotient over the
relation `Multiset.Setoid`. -/

def Multiset (α : Type) [BEq α] : Type :=
  Quotient (Multiset.Setoid α)

/- 1.2 (3 points). Now we have a type `Multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the multiplicities
of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def Multiset.mk {α : Type} [BEq α] : List α → Multiset α :=
  Quotient.mk (Multiset.Setoid α)

def Multiset.empty {α : Type} [BEq α] : Multiset α :=
  sorry

def Multiset.singleton {α : Type} [BEq α] (a : α) : Multiset α :=
  sorry

def Multiset.union {α : Type} [BEq α] : Multiset α → Multiset α → Multiset α :=
  Quotient.lift₂
  sorry
  sorry

/- 1.3 (4 points). Prove that `Multiset.union` is commutative and associative
and has `Multiset.empty` as identity element. -/

@[autograded 1]
theorem Multiset.union_comm {α : Type} [BEq α] (A B : Multiset α) :
  Multiset.union A B = Multiset.union B A :=
  sorry

@[autograded 1]
theorem Multiset.union_assoc {α : Type} [BEq α] (A B C : Multiset α) :
  Multiset.union (Multiset.union A B) C =
  Multiset.union A (Multiset.union B C) :=
  sorry

@[autograded 1]
theorem Multiset.union_iden_left {α : Type} [BEq α] (A : Multiset α) :
  Multiset.union Multiset.empty A = A :=
  sorry

@[autograded 1]
theorem Multiset.union_iden_right {α : Type} [BEq α] (A : Multiset α) :
  Multiset.union A Multiset.empty = A :=
  sorry


/- ## Question 2 (3 points + 1 bonus point): Strict Positivity

So far, we've seen a few ways Lean prevents us from breaking the soundness of
its underlying logic: requiring well-founded recursion, using type universes to
avoid Russell's Paradox, and disallowing large elimination from `Prop`. In this
problem, we'll explore another logical "safety feature": *strict positivity* of
inductive definitions.

Strict positivity requires that in any constructor definition for an inductive
type `t`, if any argument to the constructor has a (dependent or simple)
function type, then `t` may only appear as the "result" (i.e., on the right-hand
side) in that `Π` type. Such an occurrence of `t` is known as a *positive*
occurrence.

As an example, `Legal` obeys strict positivity:

  inductive Legal : Type
    | mk : (Unit → Legal) → Legal

But `Illegal` does not (this would not compile):

  inductive Illegal : Type
    | mk : (Illegal → Unit) → Illegal

In this question, we'll exemplify why Lean must require strict positivity.

**Note**: In order to declare and use the illegal type `Self` in this problem,
we must use the `unsafe` keyword for our declarations, which disables safety
features like positivity checking. Be careful: `unsafe` disables *many* safety
checks, including well-founded recursion checks. This means that Lean won't
complain if, for instance, you write `unsafe def uhOh : False := uhOh`. However,
when grading your code, we will require that all declarations (besides `Self`)
be "safe" Lean declarations -- i.e., if you removed the `unsafe` keywords and
somehow persuaded Lean to accept `Self` as a legal inductive definition, all of
your declarations should compile without errors (in particular, you shouldn't
have any infinite recursion!).

We define `Self`, an inductive type that does not obey strict positivity, below.
-/

unsafe inductive Self (α : Type) : Type
  | mk : (Self α → α) → Self α

/- 2.1 (1 point). Complete the definition below that produces a value of type
`Empty` given a value of type `Self Empty`. -/

@[autograded 1] unsafe def empty_of_self_empty : Self Empty → Empty
  := sorry

/- 2.2 (1 point). Construct a value of type `Self Empty` below.

Remember not to accidentally refer to `self_empty` itself in your definition!
For an example of what is *not* allowed, try

  unsafe def self_empty : Self Empty := self_empty

-/

@[autograded 1] unsafe def self_empty : Self Empty :=
  sorry

/- 2.3 (1 point). Use the preceding declarations to prove `False`.

Hint: recall `Empty.elim`. -/

@[autograded 1] unsafe def uh_oh : False :=
  sorry

/- 2.4 (1 bonus point). In fact, we can use `Self` to define a
*fixed-point combinator*, which allows us to write recursive functions without
relying on Lean's built-in recursive function support (which checks for things
like well-founded recursion). This should immediately raise red flags from a
soundness perspective: if we can write recursive functions without ensuring
well-founded recursion, then we can define functions satisfying, e.g.,
`f 0 = f 0 + 1`, which we have previously shown to enable a proof of `False`.

Formally, a fixed-point combinator is a function `fixp` such that for any
function `f` (if `f` has a fixed point, which we can assume it does), we have
`fixp f = f (fixp f)` (i.e., for all `x`, `fixp f x = f (fixp f) x`).

Below, use `Self` to implement a *non-recursive* function `fixp` that behaves as
a fixed-point combinator. To check your work, provide a *non-recursive* function
`fib_nr` such that `fixp fib_nr` is the Fibonacci function. (Remember to make
both of these non-recursive -- otherwise, you're just relying on Lean's built-in
recursion support.)

*Hint*: while your final version of `fixp` must not be recursive, we recommend
starting by trying to implement it recursively -- follow the formal definition
above, and watch out for infinite recursion! Then, use your recursive
implementation as a conceptual guide for your non-recursive implementation using
`Self`.

If you don't have prior familiarity with fixed-point combinators, we recommend
you read the overview below before proceeding. If you are already familiar with
the concept, feel free to skip over the rest of this comment.

--------------------------------------------------------------------------------

Intuitively, a fixed-point combinator allows us to make non-recursive functions
recursive. In order to do so, we define our non-recursive functions with an
extra argument that we treat as a "recursive reference" to our function and use
in our function body wherever we want to make a recursive call. Then, our
fixed-point combinator "fills in" that argument with an actual reference to the
function itself. We'll illustrate how this works by defining the factorial
function using a fixed-point combinator below:

* First, we define a non-recursive function `fact_nr`:

  `def fact_nr : (ℕ → ℕ) → ℕ → ℕ := λ f n => if n = 0 then 1 else f (n - 1)`

  Notice that this function is *not* recursive! Instead, we take an extra
  argument `f` that we treat as though it were a recursive reference to this
  same factorial function (without the initial function argument). The job of
  the fixed-point combinator is to make this assumption valid!

* Next, supposing we have access to a fixed-point combinator

  `fixp : ∀ {α β : Type}, ((α → β) → α → β) → α → β`

  (think about why this is the right type!), we define

  `def fact := fixp fact_nr`

  Since this is a partial application, we have `fact : ℕ → ℕ` (you should think
  through the types yourself to verify this). Notice that `fixp` has somehow
  "filled in" the first argument `f` to `fact_nr` -- in particular, since we
  assume `fixp` is correct, it somehow manages to fill in that argument with a
  reference back to `fact` itself.

Recall that we formally defined a fixed-point combinator `fixp` as satisfying
`fixp f = f (fixp f)`. In the above, we said that `fixp fact` is essentially the
result of taking `fact` and "filling in" the first argument with a reference to
an "already-recursive" version of `fact`. So then `fact (fixp fact)` is the
result of calling `fact` with its first argument being an "already-recursive"
version of `fact`. (Why is `fixp fact` "already recursive?" Recall that its
first argument has been filled in with a recursive reference, so any time it
invokes that first argument -- which we treat as a "recursive call" -- it is in
fact recursing!) Thus, `fixp fact = fact (fixp fact)`, so this agrees with our
formal definition! -/

/- Note: if you see an error about "deep recursion," use `def` declarations
instead of `let` bindings for any helper functions. (This is a Lean bug.) -/

unsafe def fixp {α β : Type} : ((α → β) → α → β) → (α → β) :=
  sorry

def fixp_fib : (ℕ → ℕ) → ℕ → ℕ :=
  sorry

-- This should compute the Fibonacci sequence (you can use `#eval` to check
-- your work).
unsafe def fib : ℕ → ℕ := fixp fixp_fib
