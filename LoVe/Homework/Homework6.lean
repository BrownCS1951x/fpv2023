import LoVe.LoVelib
import AutograderLib


/- # FPV Homework 9: Operational Semantics

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


set_option autoImplicit false

namespace LoVe

namespace Repeat

/- ## Question 1 (5 points): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive Stmt : Type
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`.

1.1 (2 points). Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop
  | skip (s) :
    BigStep (Stmt.skip, s) s
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- 1.2 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

@[autograded 1]
theorem BigStep_ite_iff {B S s t} :
  (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) :=
  sorry

/- 1.3 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

@[autograded 2]
theorem BigStep_repeat_iff {n S s u} :
  (Stmt.repeat n S, s) ⟹ u ↔
  (n = 0 ∧ u = s)
  ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) :=
  sorry

end Repeat


-- This is a helper lemma for the question below
theorem _root_.Nat.lt_of_lt_succ_ne {k m : Nat} (hlt : k < m.succ) (hne : k ≠ m)
  : k < m :=
  Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne


/- ## Question 2 (8 points): The Untyped Lambda Calculus

(Note: this question will occasionally refer to this week's lab. You do not have
to have done the lab in order to do this problem; however, you might find it
useful to at least skim the functional semantics problem there.)

In lab, we discussed the idea of a small-step operational semantics for a
functional programming language. When defining the semantics for an imperative
language, we thought about how *statements* caused transitions of a *state*. But
in functional languages, evaluation is accomplished through *reduction* of
*expressions* themselves. That is, there is no external state undergoing
transitions; rather, expressions themselves are the object of computation, and
the semantics of a functional language specify how one expression reduces to
another.

The language in the lab demonstrated the interplay between the statics,
or type system, of a functional language and its dynamics (evaluation
semantics). In this problem, we'll just focus on dynamics; in particular, we'll
look at how we can represent and reason about a language that allows us to
define arbitrary functions using lambda abstraction. The language we'll be
reasoning about in this problem is one you may have heard of before: the
*untyped λ-calculus* (ULC). -/

namespace UntypedLambdaCalculus

/- The ULC is a minimal functional programming language. Its expressions
consist only of lambda abstractions (written `(λx. b)`, where `x` is a variable
bound in the expression `b`), variables, and function application. Here are some
valid expressions in the ULC:

* `(λx. x)`
* `(λf. f f)`
* `(λx. (λy. x))` (we often write `(λx. λy. x)` for legibility)
* `(λf. f f) (λx. x)`

We begin by representing the abstract syntax of the ULC in Lean. In the past,
we've used abstract syntax trees (ASTs) to represent language syntax. However,
with the addition of lambda abstractions, we need to be able to keep track of
and refer to bound variables in our expressions. (E.g., in the body of
`(λx. x)`, it "makes sense" to refer to the variable `x`, but a top-level term
`x` is disallowed.) Ordinary ASTs don't allow this sort of context-sensitivity:
in an AST, we have no notion of what variables are in scope to refer to in a
given term. Instead, we represent the ULC's syntax with *abstract binding trees*
(ABTs). ABTs enrich ASTs by storing information about bound variables at every
node.

The binding information we'll choose to store at each node is simply the node's
*binder depth*: that is, the number of nested lambda abstractions within which
it is located. For example, the term `f x` in `(λf. (λx. f x))` has binder depth
2, while the term `(λx. f x)` has binder depth 1 and the whole expression has
binder depth 0. We refer to terms at binder depth 0 as *closed terms*; these
are the "top-level terms" in our programs.

At first, it might seem like we're not storing enough information in our ABTs to
be able to refer to variables in our expressions. After all, how do we know
*which* three variables are bound in a term at binder depth 3? What are those
variables called? To answer this question, we need to discuss how we represent
variable terms themselves.

One option would be to represent variables as strings and refer to them by name
in our abstract representation. This approach presents some difficulties,
however: for instance, we must account for *shadowing*, as in the expression
`(λx. λx. x)`, in which the body of the lambda refers to its second argument,
not its first, even though both are named `x`. Strings, in short, seem to
introduce unnecessary confusion and overhead into what we're really trying to
do: identify which bound variables exist and, among those, which we're referring
to in a given expression.

Instead of using strings, we'll represent variables using *de Bruijn indices*
("Bruijn" is pronounced as either "broin" or "brown"). De Bruijn indices
represent the "distance" -- the number of intervening lambda binders -- between
the use of a variable and the site at which it's bound. In other words, a de
Bruijn index tells you how many nested lambdas you have to jump before getting
to the one that binds the variable you're referring to. Here are some examples
(we modify our notation a bit, since our variables no longer have string names):

* `(λ. 0)` is equivalent to `(λx. x)`
* `(λ. λ. 1)` is equivalent to `(λx. λy. x)`
* `(λ. λ. 0 1)` is equivalent to `(λx. λf. f x)`

With the power of de Bruijn indices, you might wonder why we even need ABTs
at all -- couldn't we simply have a constructor `Term.var : Nat → Term` in a
regular AST that carries the de Bruijn index of its referent? (In fact, as we
will see, this is actually how Lean represents its variables!) Recall, however,
that one of the key functions of ABTs is to tell us *which* variables we can
refer to in a given scope. Using the approach just mentioned, we could write the
term `Term.var 15`, which is a nonsensical program -- there are no binders at
all to which our variable could point, let alone 15 of them! The role of the
binder depth information in our ABTs, then, is to restrict which de Bruijn
indices may legally appear in a given expression. In general, a de Bruijn index
`i` can only occur within an expression at a binder depth of at least `i + 1`.
We enforce this by representing de Bruijn indices not as `Nat`s but as values of
type `Fin n` for some binder depth `n`. `Fin n` is simply the type of natural
numbers strictly less than `n`.

With all of this in mind, we define below the type of ABTs for the ULC. Take a
moment (or several!) to see how everything we have just discussed fits together.
-/

-- A `Term` is parametrized by a `Nat` representing its binder depth.
inductive Term : Nat → Type
  -- A `var`iable contains the de Bruijn index of its referent, which is
  -- strictly less than its own binder depth.
  | var  {n : Nat} : Fin n → Term n
  -- A `lam`bda term binds a variable and carries a body in which that variable
  -- is bound, making the body's binder depth one greater than that of the
  -- lambda itself.
  | lam  {n : Nat} : Term n.succ → Term n
  -- Function `app`lication simply consists of two terms (the function and the
  -- argument), each at the same binder depth.
  | app  {n : Nat} : Term n → Term n → Term n

-- Closed terms are terms at binder depth 0. Note that we use `abbrev` for
-- technical reasons; you can treat this like a `def`.
abbrev ClosedTerm := Term 0

-- Feel free to ignore this line
deriving instance Repr for Term

-- This line allows us to write, e.g., `var n` instead of `Term.var n`
open Term

/- We provide a `toString` function for printing out expressions in a readable
format. We demonstrate its use in the examples below. -/
protected def Term.toString {n : Nat} : Term n → String
  | var n   => toString n.val
  | lam b   => "(λ. " ++ b.toString ++ ")"
  | app f x => "(" ++ f.toString ++ " " ++ x.toString ++ ")"
instance {n : Nat} : ToString (Term n) := ⟨Term.toString⟩

/- Here are some examples of (closed) terms of the ULC together with their
corresponding `ClosedTerm` representations: -/

-- `(λx. x)`
def demoId : ClosedTerm := lam (var 0)
#eval toString demoId

-- `(λf. λx. f x)`
def demoApp : ClosedTerm := lam (lam (app (var 1) (var 0)))
#eval toString demoApp

/- 2.1 (2 points). And now two for you to try: fill in `comp` and `someNonsense`
with the `ClosedTerm` corresponding to the expression above each declaration.
`someNonsense` reveals an interesting feature of de Bruijn indices that differs
from the string representation of variables! (Hint: look at the two occurrences
of `f` in your de Bruijn representation.)

Hint: Use `#eval` with `toString` to view your answers in a more readable
format! -/

-- `(λg. λf. λx. g (f x))`
def comp : ClosedTerm :=
  sorry

-- `(λf. f (λg. g f))`
def someNonsense : ClosedTerm :=
  sorry

/- Now that we've defined the syntax of the ULC, we need to specify its
semantics! Once again, lambda abstractions turn out to be tricky: in particular,
we need a way to represent the process of *substitution*. This is the operation
we perform when we "plug in" an argument to a function; we see this in Lean when
we reduce the expression `(fun x => x + x) 4` to `4 + 4`.

We define the substitution operation below as the function `subst` on terms,
which takes as arguments the body of a lambda abstraction and the argument to
fill in for the variable it binds. So, e.g., if we wanted to evaluate
`(λ. f f) (λx. x)`, we would call `subst` with `f f` as its first argument and
`(λx. x)` as its second. `subst` would then return the term `(λx. x) (λx. x)`,
"filling in" `(λx. x)` for `f` everywhere `f` appears in the body. (Note: we'll
continue to use string variable names in prose for convenience; in practice, of
course, these would be de Bruijn indices.) More generally, the term
`app (lam b) x` will reduce to `subst b x` (we'll formalize this shortly).

Notice that the first argument to `subst` is *not* closed! It contains a free
variable -- the one bound in the lambda abstraction from which the body is taken
-- and it is this variable (and only this variable!) for which the second
argument to `subst` should be substituted. (E.g., if the first argument to
`subst` were instead `f g` in the example above, then only `f` would become
`(λx, x)` in the result.)

2.2 (2 points). Below, we've given you a skeleton for the `subst` function
described above. Your task is to complete the implementation.

Important Note 1: We mentioned earlier that `Fin n` is the type of natural
numbers less than `n`. This is achieved using a *dependent product type*:
`Fin n = (k : Nat) × (k < n)`. In other words, terms of type `Fin n` are pairs
consisting of a number less than `n` and a proof of that inequality. You can
write a term of type `Fin n` as `⟨k, hk⟩` where `k : Nat` and `hk : k < n`
(notice that we use angled brackets, not parentheses, for dependent pairs). This
is demonstrated in the pattern-matching we've provided.

Important Note 2: `if h : k = m ...` is a *dependently-typed* if-then-else
expression. This means that, within the `then` branch, you'll have in your
context `h : k = m`, and in the `else` branch, you'll have `h : k ≠ m`. You will
find this useful for generating the proof terms needed to produce terms of `Fin`
types.

Important Note 3: If we have a valid term at binder depth `n`, then it is also
a valid term at any deeper binder depth. (Think about why this is -- why don't
we have to, for instance, change any de Bruijn indices?) We have provided you
with a helper function `push` that "casts" a `Term` from one binder depth to a
deeper one. You will find this useful when implementing `subst`. -/

#check Nat.zero_le
#check Nat.lt_of_lt_succ_ne

def push {m n : Nat} : Term m → m ≤ n → Term n
  | var ⟨k, hk⟩, h => var ⟨k, Nat.lt_of_lt_of_le hk h⟩
  | lam b      , h => lam (push b (Nat.succ_le_succ h))
  | app f x    , h => app (push f h) (push x h)

def subst {m : Nat} : (body : Term m.succ) → (arg : ClosedTerm) → Term m
  | var ⟨k, hk⟩, arg =>
    if h : k = m then
      sorry
    else
      sorry
  | lam b      , arg =>
    sorry
  | app f x    , arg =>
    sorry

/- Equipped with a definition of substitution, we can now state the semantics of
the ULC! Notice that we only define our semantics for `ClosedTerm`s: our
evaluation order is such that we only ever step expressions at the "top level."
(Note that there are other possible evaluation orders for the ULC for which this
is not the case.)

We first define our single-step transition relation. -/

inductive Step : ClosedTerm → ClosedTerm → Prop
  | app {b x}    : Step (app (lam b) x) (subst b x)
  | fn  {e e' x} : Step e e' → Step (app e x) (app e' x)

-- We define the notation `e ⇒ e'` for `Step e e'`
infix:50 " ⇒ " => Step

/- Next, as in lecture, we take the reflexive transitive closure of `Step` to
obtain the multi-step transition relation.

Note that this is slightly different from the `RTC` definition in LoVelib! -/

inductive RTC {α : Type} (P : α → α → Prop) : α → α → Prop
  | rfl   {x : α}     : RTC P x x
  | trans {x y z : α} : P x y → RTC P y z → RTC P x z

-- We define the notation `e ⇒* e'` for `RTC Step e e'`
infix:50 " ⇒* " => RTC Step

/- 2.3 (1 point). While our formalisms are useful for reasoning about the ULC,
we also want to be able to run our ULC programs! Implement the function `eval`
below that evaluates a term of the ULC *according to the reduction rules we*
*formalized above.* `eval` should *fully* reduce its argument: if we have
`e ⇒* e'` such that `e'` does not step to any term, then `eval e` should
evaluate to `e'`; if `e` steps infinitely, `eval e` should fail to terminate.
Notice that `eval` has been marked `unsafe` because of this second eventuality.
(Because of this, we can't prove anything about `eval` -- in particular, we
can't prove that it agrees with `Step`. Instead, you'll want to use some test
cases -- using `#eval` and `toString` -- to check your work.) -/

unsafe def eval : ClosedTerm → ClosedTerm
  := sorry

/- In the lab, we discussed the concept of *progress*: the property of a (typed)
language that ensures that no well-typed term "gets stuck" during evaluation:
any well-typed term either is a value or can take a step according to our
semantics. Recall that a *value* is an expression that we consider to be "fully
evaluated" (e.g., `42` and `"Hi"` are values in Lean, whereas `20 * 2 + 2` and
`"H" ++ "i"` are not).

In this problem, we're working with an untyped language, so we can't quite state
progress as such (there's no notion of a "well-typed term"). However,
conveniently, we've formulated our representation of terms in such a way that
*every* term we can write down turns out to be "valid": there is no way to
represent a term that we haven't "accounted for" in our semantics. Thus, we can
state a sort of "quasi-progress" criterion that holds of our ULC semantics:
every term either is a value or steps to some other term.

But what is a value in the ULC? Well, the only kind of expression that can't
be further reduced is a lambda-abstraction: on its own, `(fun x => x)` does not
simplify to anything in Lean, and likewise for the ULC. Therefore, we'll define
a `Value` predicate that specifies the values of the ULC to be precisely those
terms that are lambda abstractions. -/

inductive Value : ClosedTerm → Prop
  | lam (b : Term 1) : Value (lam b)

/- 2.4 (2 points). Equipped with this definition, your task is to prove the
quasi-progress property below.

Note: due to limitations of Lean, you won't be able to use the `induction`
tactic here. Instead, you'll need to use `cases` and obtain an IH by explicitly
invoking `quasiprogress` recursively (e.g.,
`have ih := quasiprogress someTermHere`). Make sure your recursion is valid! -/

@[autograded 2]
theorem quasiprogress : ∀ t : ClosedTerm, Value t ∨ (∃ b', t ⇒ b') :=
  sorry

/- 2.5 (2 points). The functional language we presented in the lab had an even
stronger guarantee than progress: every well-typed term not only stepped to some
other term, but would, in finitely many steps, eventually reduce to a value.
This property is known as *termination*, and it is one that the ULC does not
have. That is, there is some term (in fact, there are many) in the ULC that is
*nonterminating* -- we can keep applying reduction rules to it forever and never
get a value. Your task is to prove this fact.

We define a predicate `Nonterminating : ClosedTerm → Prop` such that
`Nonterminating t` holds just when `t` is nonterminating as described above
(i.e., `t` never steps to a value). (It might look at first glance like
`Nonterminating` isn't quite strong enough, but remember that `quasiprogress`
guarantees that every term will step to some other one!) We use this definition
to state the `nontermination` theorem below (for you to prove).

There are a number of ways to go about proving `nontermination`. However, the
most straightforward way (and the one we've given you some helper lemmas to
facilitate) is by coming up with a term that transitions to itself
*in a single step* and exploiting this property. -/

def Nonterminating (t : ClosedTerm) : Prop :=
  ¬∃ t', t ⇒* t' ∧ Value t'

-- You will likely find the lemma `rtc_step_self_of_step_self` below helpful.
-- (Note: we don't expect you to follow the proof below!)
theorem rtc_step_self_of_step_self {t t' : ClosedTerm} :
  t ⇒ t → t ⇒* t' → t' = t :=
  λ hloop hrtc =>
    hrtc.rec
      (λ _ => rfl)
      (λ hstep _ heq hloop =>
        have h := step_det hloop hstep
        h ▸ heq (h ▸ hloop))
    hloop
  where
    step_det {t t' t'' : ClosedTerm} : t ⇒ t' → t ⇒ t'' → t' = t''
      | .app, .app => rfl
      | .fn h, .fn h' => step_det h h' ▸ rfl

@[autograded 2]
theorem nontermination : ∃ t : ClosedTerm, Nonterminating t :=
  sorry

end UntypedLambdaCalculus


end LoVe
