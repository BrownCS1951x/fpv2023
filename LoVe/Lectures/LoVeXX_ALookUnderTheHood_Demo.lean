/- Copyright © 2023 Robert Y. Lewis. See `LICENSE.txt`. -/

import Lean
import LoVe.LoVelib

/- 

# Data structures and processes of a proof assistant 

Today will be a break from the normal flow of things.
We'll set down some vocabulary for different parts of the 
proof assistant processing pipeline, and talk about some of the
algorithms involved.


## Elaboration

There's a big gap between Lean "input syntax" and actual 
dependent type theory.

-/


#check 1 + 2 

set_option pp.all true in 
#check 1 + 2

/-
*Elaboration* is the art of going from input syntax 
to the abstract syntax of our language. 
This happens in most languages to some degree,
but it's especially complicated in languages with lots of 
implicit information!
-/

/-

## Expressions/abstract syntax

What is the abstract syntax of Lean anyway?
-/

#print Lean.Expr 

-- let's write the corresponding expr
#check fun b : Bool => not b 

section 
open Lean Expr 


end 

/-

## Declarations 

A declaration is essentially a triple of 
* a name
* an expr (the type)
* an expr (the body)

-/ 

def f : Bool → Bool := fun b => not b 

#print Lean.Declaration 

/-

The `def` and `theorem` commands take in these components.
They elaborate the type and body, and check that the 
type of the body is the same as the type of the declaration.



## Environments

At any point in a Lean file, we can access and use everything
that was declared before that point.

We call this collection an *environment*.
Essentially, an environment is a set of declarations. 

Elaboration has access to the environment!

-/

#print Lean.Environment 


/-

## Tactics 

Where do tactics fit into this picture?

-/

theorem a_silly_theorem : True := 
And.left (And.intro (by simp) trivial)

#print a_silly_theorem 





/-

During elaboration, tactics are evaluated to produce expressions.
The environment stores no trace of a tactic.

Tactics are, essentially, functions from "proof states"
to expressions.

Notice that, to get an "expected type," elaboration must have begun 
in order for the tactic to execute.
But also, tactic evaluation can effect elaboration!

-/

#check id (by exact (5 : ℤ))

/-

There's a very complicated dance here. 
Also relevant: type class inference.



## Type checking


The elaborator, and the tactic execution engine, both seem to 
have some notion of type correctness.

-/

#check Nat.add 4 (-2 : ℤ) 

example : False := by 
  exact trivial 

/-

These algorithms are horrendously complicated. 
Even worse, tactics are arbitrary programs that can do all kinds
of stupid awful things. 
Why can we trust that they aren't compromising the soundness 
of our system?
-/

elab "remove_goals" : tactic => Lean.Elab.Tactic.setGoals []

example : False := by 
  remove_goals


/-

What does "soundness" even mean?










**Theorem (soundness)**. In an environment in which no new axioms 
have been declared, there is no well-typed declaration with type `False`.









The *kernel* is our last resort against soundness bugs.
No matter what the elaborator does, it must submit any potential
new declaration to the kernel for inspection.

The kernel implements a slow, simple, reliable type checking algorithm.
It is small (in terms of LOC) and well documented.

Furthermore, it can "export" an entire environment.
External programs that implement type checking algorithms for the same 
type theory can read this export and double check that there is
no type error.

-/




/-
## A language hierarchy 

In summary, we have a bunch of different languages here.

input language <---> tactic language
     |               /
     | elaboration  /
     v             v
     core language
        |
        | kernel export
        v 
  export language


It seems reasonable to have the input and core languages
be similar. 

What should the export language look like?
What about the tactic language?

-/