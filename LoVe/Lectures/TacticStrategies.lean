import LoVe.LoVelib
import Mathlib.Tactic.Linarith

open Qq

/-!

# Proof by reflection

YOu may have noticed that we can't prove anything about the tactics we write.
But there's a middle ground: sometimes with a bit of meta "wrapper code,"
we can turn proofs about syntax-like operations into actual proof terms.

The general strategy looks like this:
* represent the syntax of some class of formulas in (non-meta) Lean
* define an interpretation function from these formulas to Prop
* define some operation on this syntax, and prove it correct with respect to the interpretation
* write a small bit of meta code that turns a goal into a statement about your reflected syntax

The idea is that the goal left after applying your correctness theorem can be proved by computation.

This is commonly used for evaluation or normalization functions.
`ring`, for example, can be implemented by defining the syntax of ring expressions
and verifying a normalization algorithm:
if
`ring_syntax : Type`,
`interp {α : Type} [ring α] : ring_syntax → α`,
`normalize : ring_syntax → ring_syntax`, then
`∀ r1 r2 : ring_syntax, interp r1 = interp r2 ↔ normalize r1 = normalize r2`.

The meta code looks at a goal `c + a*b = b*a + c`,
constructs `ring_syntax` objects `r1` and `r2` representing both sides,
and changes the goal to showing that `normalize r1 = normalize r2`.
This can be proved by `refl`.

-/

inductive bexpr
| atom : Bool → bexpr
| and : bexpr → bexpr → bexpr
| or : bexpr → bexpr → bexpr
| imp : bexpr → bexpr → bexpr
| not : bexpr → bexpr

open bexpr

def interp : bexpr → Prop
| (atom true) => True
| (atom false) => False
| (bexpr.and a b) => interp a ∧ interp b
| (bexpr.or a b) => interp a ∨ interp b
| (imp a b) => interp a → interp b
| (bexpr.not b) => ¬ interp b

def normalize : bexpr → Bool
| (atom b) => b
| (bexpr.and a b) => normalize a && normalize b
| (bexpr.or a b) => normalize a || normalize b
| (imp a b) => (! (normalize a)) || normalize b
| (bexpr.not b) => ! (normalize b)

theorem normalize_correct (b : bexpr) : normalize b = true ↔ interp b :=
by
  induction b with
  | atom a => cases' a <;> simp [normalize, interp]
  | and a b iha ihb => simp [normalize, interp, *]
  | or a b iha ihb => simp [normalize, interp, *]
  | not b ih =>
    simp [normalize, interp]
    rw [Bool.eq_false_iff]
    tauto
  | imp a b iha ihb =>
    simp [normalize, interp, ← iha, ← ihb]
    rw [Bool.eq_false_iff]
    tauto

open Lean Meta Tactic Elab Tactic

#check Expr.forallE

partial def bexprOfExpr (e : Q(Prop)) : MetaM Expr :=
match e with
| ~q(True) => mkAppM `bexpr.atom #[mkConst ``true]
| ~q(False) => mkAppM `bexpr.atom #[mkConst ``false]
| ~q($a ∧ $b) => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.and #[a', b']
| ~q($a ∨ $b) => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.or #[a', b']
| Expr.forallE _ a b _  => do
  let a' ← bexprOfExpr a
  let b' ← bexprOfExpr b
  mkAppM `bexpr.imp #[a', b']
| ~q(¬ $a) => do
  let a' ← bexprOfExpr a
  mkAppM `bexpr.not #[a']
| _ => failure

def changeGoal : TacticM Unit := withMainContext <| do
  let t ← getMainTarget
  let t' : Q(bexpr) ← bexprOfExpr t
  let gl ← getMainGoal
  let gls ← gl.apply q(Iff.mp (normalize_correct $t'))
  setGoals gls

elab "change_goal" : tactic => changeGoal


example : (True → True) ∨ False := by
  change_goal
  rfl

/-!
You could imagine doing the same with, say, a SAT solver.

Modify `bexpr` to cover all propositional formulas: `atom : ℕ → bexpr`.
Add an argument to `interp`: `dict : ℕ → Prop` assigning atoms to propositions.
`normalize` becomes `is_tautology : bexpr → bool`.
`normalize_correct` becomes
  `is_tautology_correct (b : bexpr) : is_tautology b = tt ↔ ∀ dict, interp dict b`
`bexpr_of_expr` will also have to return a dictionary.

-/



/-!

# Linear arithmetic

We've used the tactic `linarith` to prove statements that follow from linear
(in)equalities in the local context.

For convenience we will work over a linear ordered ring, although this makes sense
with weaker assumptions.

An expression is *linear* in variables `x₁ ... xₙ` if it is a polynomial of degree
at most one: that is, it is a sum of products `cᵢ * xᵢ`, where each `cᵢ` is a
coefficient.

The key point: variables are not multiplied together.
`5*x + 3*y` is linear, but `5*x*y` is not.

An (in)equality is linear if it is of the form `a ⋈ b`, where
⋈ is <, ≤ =, ≥, or >, and a and b are linear expressions.
-/


example (ε : ℚ) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε :=
 by linarith

example (g v V c h : ℚ) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
         (h5 : 0 ≤ c) (h6 : c < 1) :
  v ≤ V :=
by linarith

example (N : ℕ) (n : ℕ) (A : ℚ) (l : ℚ) (Hirrelevant : n > N)
        (h : A - l ≤ -(A - l)) (h_1 : ¬A ≤ -A) (h_2 : ¬l ≤ -l) (h_3 : -(A - l) < 1) :
  A < l + 1 :=
by linarith


/-!
We're interested in the problem of deciding whether a system of linear
inequalities is *satisfiable*:

Given
    h1 : a₁¹x₁ + a₂¹x₂ + ... + aₙ¹xₙ ⋈¹ 0
    h2 : a₁²x₁ + a₂²x₂ + ... + aₙ²xₙ ⋈² 0
    h3 : a₁³x₁ + a₂³x₂ + ... + aₙ³xₙ ⋈³ 0
    ...
    hk : a₁ᵏx₁ + a₂ᵏx₂ + ... + aₙᵏxₙ ⋈ᵏ 0

is there an assignment of variables to values
    x₁ ↦ v₁, x₂ ↦ v₂, ..., xₙ ↦ vₙ
that makes each of h1 ... hk true?



Note: if we can decide this, we can decide implications like in the examples above.
For a linear inequality `h`,
the implication `(h1 ∧ h2 ∧ ... ∧ hk) → h` is valid exactly when the system
`h1, h2, ... hk, ¬ h` is unsatisfiable.




## Verified decision procedures

To implement a tactic like `linarith`, we need to do more than just decide
these kinds of statements: we need to prove that our decisions are correct.

What are our options here?

### Proof by reflection

We talked about proof by reflection on Monday.
To do this, we'd have to represent the syntax of linear expressions as a datatype,
define our decision procedure in Lean,
and prove that it's correct with respect to an interpretation function.


This is probably doable! But executing our decision procedure would happen
in Lean's (slow, reliable) kernel. All numeric arithmetic would be done in unary.


### "Prove-as-we-go"

The simple tactics we implemented just updated the goal and context directly.
Presumably, some decision procedures here will make intermediate claims:
they'll start with h1 ... hk, derive new facts from those,
derive new facts from those, ...
We could imagine a tactic that just fills up the local context with new conclusions,
until it proves the goal or terminates. (Details depending on the algorithm.)

Is this efficient? It depends on how much unnecessary work the tactic does...


### Certificate checking

Our input is
    h1 : a₁¹x₁ + a₂¹x₂ + ... + aₙ¹xₙ ⋈¹ 0
    h2 : a₁²x₁ + a₂²x₂ + ... + aₙ²xₙ ⋈² 0
    h3 : a₁³x₁ + a₂³x₂ + ... + aₙ³xₙ ⋈³ 0
    ...
    hk : a₁ᵏx₁ + a₂ᵏx₂ + ... + aₙᵏxₙ ⋈ᵏ 0
and our goal is to prove `false`.
We can assume that each ⋈ⁱ is <, ≤, or =.

Suppose we had an oracle that produced a list of nonnegative coefficients
c₁ ... cₖ such that
* c₁ * (a₁¹x₁ + a₂¹x₂ + ... + aₙ¹xₙ) + c₂ * (a₁²x₁ + a₂²x₂ + ... + aₙ²xₙ)
  + ... + cₖ * (a₁ᵏx₁ + a₂ᵏx₂ + ... + aₙᵏxₙ) = 0
* For at least one i, cᵢ > 0 and ⋈ⁱ is =.

We could then prove false by summing together the scaled linear expressions;
this sum must be both equal to and less than 0.

This list of coefficients c₁ ... cₖ is a *certificate* for the unsatisfiability
of the system of inequalities.

Efficiently finding such a certificate can be very hard.
But given such a certificate, it's easy to turn it into a proof term.



## Mathlib's linarith tactic

`linarith` in mathlib follows the certificate checking approach.

* Preprocessing: manipulate the context and goal to prepare for the main tactic.
* Parsing: find the linear structure of the hypotheses.
* Certificate generation: using these parsed linear (in)equalities, find coefficients
  c1 ... ck. (Needs: a certificate-producing oracle.)
* Validation: use this certificate to prove `0 < 0`.
  (Needs: a normalization tactic to reduce the sum of products to 0.)



Certificate generation is the computationally expensive part of this process.

Note, we don't need to assume anything about it:
the certificate procedure can be an oracle.

There are lots and lots of algorithms out there for doing this.
Simplex is a familiar and efficient technique (but can be hard to implement
efficiently in a pure functional language.)


Mathlib's approach: Fourier-Motzkin elimination.

Start with
    h1 : a₁¹x₁ + a₂¹x₂ + ... + aₙ¹xₙ ⋈¹ 0
    h2 : a₁²x₁ + a₂²x₂ + ... + aₙ²xₙ ⋈² 0
    h3 : a₁³x₁ + a₂³x₂ + ... + aₙ³xₙ ⋈³ 0
    ...
    hk : a₁ᵏx₁ + a₂ᵏx₂ + ... + aₙᵏxₙ ⋈ᵏ 0

Pick a variable to eliminate: let's say xₙ.

Partition h1...hk into three sets pos, zero, neg:
    pos  = {hi | aₙⁱ > 0}
    zero = {hi | aₙⁱ = 0}
    neg  = {hi | aₙⁱ < 0}

Set aside zero; xₙ has already been eliminated from these.

For each pair of hp ∈ pos and hn ∈ neg:
* find positive cp, cn such that `cp*aₚ + cn*aₙ = 0`.
* compute the sum `cp*hp + cn*hn`. This is a new comparison.
* add this sum to the set zero, tracking that it was derived from
  (cp, hp) and (cn, hn).

After this process, zero is a set of comparisons that do not contain xₙ.

Theorem: over a dense linear ordered field,
the initial set {h1, ... hk} is satisfiable
iff the new set zero is satisfiable.

So, by successively eliminating all of the variables from our initial system,
we end up with a list of comparisons 0 ⋈ⁱ 0.
If any ⋈ⁱ is <, we've found a contradiction.
Tracing the history of how this comparison was derived, we can compute how many
copies of each original hi were added to derive it.
This produces the certificate we wanted.



But: nothing about the rest of linarith assumes that this is the algorithm
used to generate certificates. It just needs a valid certificate in the right format.

We can use external software such as Mathematica to generate these:
perhaps more efficiently, perhaps not.



## Nonlinear arithmetic

You can imagine problems that are just outside this framework.

-/

example (x y : ℚ) : 0 ≤ x*x + y*y :=
by linarith

/-!
Turns out: these problems are also decidable!

(Old result by Tarski; modern algorithms like cylindrical algebraic decomposition)

But algorithms are very slow, and/or hard to produce proofs.

Hard to separate *proof search* from the ultimate proof:
the justification is that the entire search was carried out correctly.



But for tactic implementations, we don't necessarily need decision procedures.
-/

example (x y : ℚ) : 0 ≤ x*x + y*y :=
by nlinarith
