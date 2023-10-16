import LoVe.LoVelib
import AutograderLib


/- # FPV Homework 5: Inductive Predicates

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


set_option autoImplicit false

namespace LoVe


/- ## Question 1 (4 points): A Type of Terms

The *simply typed lambda calculus* is a very basic version of the language of 
Lean. In this language we have only variables, lambda expressions (a.k.a. 
anonymous functions), and applications.

Here are some examples of terms in this language:

* `y`, a variable
* `λ x, x`, an anonymous function mapping `x` to `x`
* `(λ x, x) y`, the application of a function to a variable.


We can define a type representing the terms of this language:
 -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1 (2 points). Define an inductive predicate `IsApp` on `Term`s that is true
if and only if its argument is of the form `Term.app …`. -/

-- enter your definition here

/- 1.2 (2 points). Define an inductive predicate `IsLamFree` that is true if
and only if its argument is a term that contains no λ-expressions. -/

-- enter your definition here


/- ## Question 2 (4 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `Even`,
and should not rely on `Even`. -/

inductive Odd : ℕ → Prop
-- supply the missing cases here

/- 2.2 (1 point). Give *proof terms* for the following propositions, based on
your answer to question 2.1. -/

@[autograded 0.5] theorem Odd_3 :
  Odd 3 :=
  sorry

@[autograded 0.5] theorem Odd_5 :
  Odd 5 :=
  sorry

/- 2.3 (1 point). Prove the following theorem by rule induction: -/

@[autograded 1] theorem Even_Odd {n : ℕ} (heven : Even n) :
  Odd (n + 1) :=
  sorry

/- 2.4 (1 point). Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → false`. -/

@[autograded 1] theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
  ¬ Odd n :=
  sorry


infixl:50 " <+ " => List.Sublist

namespace NoDupSublists

/- ## Question 3 (4 points): Duplicate-Free Sublists

In this problem, we'll use inductive predicates to prove that the sublist of a
list that contains no duplicates also contains no duplicates. (Informally, a
*sublist* of a list `ys` is a list `xs` such that every element of `xs` appears
in the same order in `ys`.)

The predicate `List.Sublist : ∀ {α : Type}, List α → List α → Prop`, which
formally specifies the notion of a sublist, is defined as follows:

  inductive Sublist {α} : List α → List α → Prop
    | slnil : Sublist [] []
    | cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
    | cons₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

We've defined syntactic sugar for the sublist predicate: we can write `xs <+ ys`
instead of `List.Sublist xs ys`.

Here are some examples:
* `[] <+ [1, 2, 3]`
* `[2, 3] <+ [2, 3, 4]`
* `[2, 3] <+ [1, 2, 4, 3]`

And here are some non-examples:
* `¬([1] <+ [2, 3])`
* `¬([2, 2] <+ [2, 3])`
* `¬([2, 2, 3, 3] <+ [2, 3, 2, 3])`

Make sure to convince yourself that the sublist predicate above correctly
captures this notion of sublist.

We'll also need a couple of additional predicates in order to state the desired
theorem.

3.1 (1 point). Define a predicate `IsIn` such that `IsIn x xs` holds precisely
when `x` is an element of the list `xs`.

Note: you may not use *any* external inductive or recursive definitions besides
the `List` constructors in your solution. (Of note, this means that
`List.Sublist` and the equality operator `=` are not allowed.) -/

-- Fill this in:
inductive IsIn {α : Type} : α → List α → Prop


-- For the rest of this problem, we'll redefine the `∈` and `∉` notation to use
-- your `IsIn` predicate instead of the default.
scoped infix:50 (priority := high) " ∈ " => IsIn
scoped notation:50 (priority := high) x:50 " ∉ " xs:50 => Not (IsIn x xs)

/- 3.2 (1 point). Define a predicate `NoDuplicates` such that `NoDuplicates xs`
holds precisely when the list `xs` does not contain any duplicate elements.

Here are some examples:
* `NoDuplicates []`
* `NoDuplicates [tt]`
* `NoDuplicates [2, 1, 3]`

And here are some non-examples:
* `¬(NoDuplicates [tt, tt])`
* `¬(NoDuplicates [1, 9, 5, 1])`
* `¬(NoDuplicates [3, 1, 4, 1, 5])`

Note: you may not use the equality operator `=`, `List.append` (aka `++`), or
`List.Sublist` in your solution.

Hint: you may find the `IsIn` (`∈`) predicate you defined above useful! -/

-- Fill this in:
inductive NoDuplicates {α : Type} : List α → Prop


/- 3.3 (2 points). Equipped with these definitions, prove the theorem we stated
at the beginning: the sublist of a duplicate-free list is also duplicate-free.
Choose what to induct on wisely!

Hint: Recall that you can generalize your induction over a variable you've
previously bound (so long as the thing you're inducting on doesn't depend on it)
using the `generalizing` keyword. If you find yourself at a point in your proof
where your IH doesn't match your goal because it fixes some variable you're not
inducting on, you may need to generalize your induction over that variable. -/

-- You may find this helper lemma useful when writing your proof. (It's possible
-- to prove this, but we're giving it to you for free.)
@[legalAxiom]
axiom not_in_of_not_in_sublist {α : Type} {x : α} {xs ys : List α} :
  xs <+ ys → x ∉ ys → x ∉ xs

@[autograded 2]
theorem noDuplicates_sublist_of_noDuplicates {α : Type} (xs ys : List α) :
  NoDuplicates ys → xs <+ ys → NoDuplicates xs :=
  sorry

end NoDupSublists

end LoVe
