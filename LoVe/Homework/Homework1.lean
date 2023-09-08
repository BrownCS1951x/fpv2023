import LoVe.LoVelib
import AutograderLib

/- # Homework 1: Definitions and Statements

The goal of this homework is to get you used to interacting with Lean.
We're not doing any *proving* yet, just some defining!

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finsihed, submit *only* this file to the appropriate Gradescope assignment.

When you submit to Gradescope, problems tagged as `autograded` will be
autograded. *This is not your final grade*; a significant portion of the
assignment will be manually graded. Therefore, you should still check your
submission for completeness and correctness even if the autograder does not
produce errors. -/

namespace LoVe

set_option autoImplicit false

/- ## Question 1 (6 points): Terms

We start by declaring three new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type

/- 1.1 (4 points). Complete the following definitions by replacing the `sorry`
placeholders with terms of the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

@[autograded 1] def B : (α → β) → (γ → α) → γ → β :=
  sorry

@[autograded 1] def S : (α → β → γ) → (α → β) → α → γ :=
  sorry

@[autograded 1] def moreNonsense : (γ → (α → β) → α) → γ → β → α :=
  sorry

@[autograded 1] def evenMoreNonsense : (α → α → β) → (β → γ) → α → β → γ :=
  sorry

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse." -/

@[autograded 2] def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  sorry




/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `S` above, using ASCII or
Unicode art. You might find the characters `–` (to draw horizontal bars) and `⊢`
useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- Write your solution here





/-! ## Question 3 (3 points): Implicit Arguments

In this question, we'll show you some useful syntax features of Lean that will
appear throughout the semester.

There are times when arguments can be inferred easily from context -- there is
only one value they could possibly be. In those cases, it is convenient not to
have to explicitly specify such arguments when calling a function. This mainly
happens with type inferences: a type argument to a function can be inferred from
the types of the arguments that follow.

For example, we define the `append` function for lists: -/

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- Because `append` must work for any type of list, the type of the list's
elements is provided as an argument. As a result, the type must be provided in
every call (though we can wite `_` to ask Lean to infer the type).

Note that we use the following convenience notation: `[]` for `List.nil`,
`x :: xs` for `List.cons x xs`, and `[x₁, …, xN]` for `x₁ :: … :: xN :: []`. -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]
#eval append Bool [true] [true, false]

/- If the type argument is enclosed in `{ }` rather than `( )`, it is implicit
and need not be provided when calling the function (Lean will attempt to infer
it). -/

-- This is defined in the library as `List.append`
def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]
#eval appendImplicit [true] [true, false]

/- 
Notice that we did not need to give the argument `ℕ` or `Bool` to 
`appendImplicit`.

Prefixing a definition name with `@` gives the corresponding defintion in
which all implicit arguments have been made explicit. This is useful in
situations where Lean cannot work out how to instantiate the implicit
argument. -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]


/-! 3.1 (1 point). Define the function `reverse`, which takes a list (whose
elements have arbitrary type `α`) and reverses it. Write the type signature and
implement this function. Make the type `α` an implicit argument.

Hint: you might find `List.append` useful in your implementation! You can also
use the notation `xs ++ ys` for `List.append xs ys`. -/

-- write your solution here

-- Once you've written your solution, uncomment these test cases and check that
-- they give the expected outputs
-- #eval reverse [1, 2, 3, 4, 5] -- expected: [5, 4, 3, 2, 1]
-- #eval reverse ([] : List ℕ)  -- expected: []
-- #eval @reverse ℕ []          -- expected: []





/-! Notice that when the list argument to `reverse` is empty, it is not clear
what type should be filled in for `α`. (Try evaluating `reverse []`, without
explicitly specifying any types, and see what happens!) The last two examples
above demonstrate two ways to specify types when that happens.

In `reverse ([] : List ℕ)`, we added an explicit type signature to the otherwise
underspecified empty list. This forces the list to have type `List ℕ`, allowing
Lean to determine that `α` must be `ℕ`.

In `@reverse ℕ []`, we used the `@` symbol to force the implicit argument `α` to
be explicit and specify that it should be `ℕ`.

We can also specify *named* implicit arguments by using the following syntax: -/

#eval append (α := ℕ) [] []

-- For functions with multiple implicit arguments, we can also choose to specify
-- just some of the implicit arguments using named arguments.

/-! We can also used named arguments with explicit arguments, too! Notice that
in this definition, we're also using *default arguments*: if we specify `x` and
`z` but fail to specify `y` and/or `w`, `y` and/or `w` will automatically be
bound to the values `1` and/or `2`, respectively. Notice also that, using named
arguments, we can pass arguments out of order. -/

def f (x : ℕ) (y : ℕ := 1) (w : ℕ := 2) (z : ℕ) :=
  x + y + w - z

#eval f 4 1 2 3      -- 4 + 1 + 2 - 3
#eval f (z := 3) 4   -- 4 + 1 + 2 - 3
#eval f 4 (z := 3)   -- 4 + 1 + 2 - 3
#eval f 4 0 (z := 3) -- 4 + 0 + 2 - 3




/-! 3.2 (1 point). Change the value of `z` below so that the expression
evaluates to `2`.
-/

#eval f (z := 3) 1

/-! 3.3 (1 point). Specify a value for `w` below so that the expression
evaluates to `5`. -/

#eval f (y := 3) (x := 1) (z := 1)





/- ## Question 4 (5 points): Singletons and Flatten

4.1 (1 point). Define the function `singletons` that turns a list into a list of
singleton lists, where the singleton at each position contains the element in
that position in the original list.

For instance, `singletons [1, 2, 3, 4]` should evaluate to
`[[1], [2], [3], [4]]`. -/

def singletons {α : Type} : List α → List (List α)
  := sorry

/- 4.2 (2 points). Define the function `flatten` that takes a list of lists and
"flattens" it into a single list.

For example, `flatten [[1], [2, 3], [], [4]]` should evaluate to `[1, 2, 3, 4]`.

You should not call any form of append function (`++`, `List.append`, etc.) in
your solution. -/

def flatten {α : Type} : List (List α) → List α
  := sorry

/-! 4.3 (1 point). State a theorem that says that applying `singletons` and then
`flatten` to any list gives the same list you started with. -/

-- Replace `True` with your lemma statement. No need to fill in the `sorry`!
theorem flatten_singletons : True := sorry





/- 4.4 (1 point). Is it true that applying `flatten` and then `singletons` to a
list of lists gives you back the same list of lists you started with? If so,
explain why; if not, provide an example of a list for which the claim does not
hold. -/

-- Write your response to part 4 here.

end LoVe
