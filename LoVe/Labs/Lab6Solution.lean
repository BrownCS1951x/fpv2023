import LoVe.Lectures.LoVe09_OperationalSemantics_Demo


/- # FPV Lab 6: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  | seq (S T s t u) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  | loop_base (S s) :
    BigStep (Stmt.loop S, s) s
  | loop_step (S s t u) (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.loop S, t) u) :
    BigStep (Stmt.loop S, s) u

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    { intro hasn
      cases hasn
      rfl }
    { intro heq
      rw [heq]
      apply BigStep.assign }

@[simp] theorem BigStep_assert {B s t} :
  (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
  by
    apply Iff.intro
    { intro hast
      cases hast
      simp [*] }
    { intro hand
      cases hand with
      | intro hts hB =>
        rw [hts]
        apply BigStep.assert
        exact hB }

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
  (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
  by
    apply Iff.intro
    { intro hseq
      cases hseq
      apply Exists.intro
      apply And.intro <;>
        assumption }
    { intro hseq
      cases hseq with
      | intro u hand =>
        cases hand with
        | intro hS₁ hS₂ =>
          apply BigStep.seq <;>
            assumption }

theorem BigStep_loop {S s u} :
  (Stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  by
    apply Iff.intro
    { intro hloop
      cases hloop with
      | loop_base S s =>
        apply Or.inl
        rfl
      | loop_step S s t u hS hl =>
        apply Or.inr
        apply Exists.intro t
        aesop }
    { intro hor
      cases hor with
      | inl hsu =>
        rw [hsu]
        apply BigStep.loop_base
      | inr hex =>
        cases hex with
        | intro t hand =>
          cases hand with
          | intro hS hl =>
            apply BigStep.loop_step <;>
              assumption }

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
  (Stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
  by
    apply Iff.intro
    { intro hchoice
      cases hchoice with
      | choice _ _ _ i hless hbody =>
        apply Exists.intro i
        apply Exists.intro hless
        assumption }
    { intro hex
      cases hex with
      | intro i hex =>
        cases hex with
        | intro hless hstep =>
        apply BigStep.choice <;>
          assumption }

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    GCL.Stmt.assign x a
  | S; T =>
    gcl_of S;
    gcl_of T
  | Stmt.ifThenElse B S T  =>
    GCL.Stmt.choice [
      GCL.Stmt.assert B; gcl_of S,
      GCL.Stmt.assert (fun s ↦ ¬ B s); gcl_of T
    ]
  | Stmt.whileDo B S =>
    GCL.Stmt.loop
      (GCL.Stmt.assert B;
       gcl_of S);
    GCL.Stmt.assert (fun s ↦ ¬ B s)

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

/- Here are two other possibilities:

* `GCL.Stmt.loop (GCL.Stmt.assert (fun _ ↦ False))`
* `GCL.Stmt.assign "x" (fun s ↦ s "x")` -/


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
  S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
  S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
  S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
  Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by
    intro s t
    apply Iff.intro
    { intro hasn
      cases hasn
      simp [*] }
    { intro hskip
      cases hskip
      simp [*] }

theorem BigStepEquiv.seq_skip_left {S} :
  Stmt.skip; S ~ S :=
  by
    intro s t
    apply Iff.intro
    { intro hseq
      cases hseq with
      | seq _ _ _ u _ hs hS =>
        cases hs
        assumption }
    { intro hS
      apply BigStep.seq
      { apply BigStep.skip }
      { assumption } }

theorem BigStepEquiv.seq_skip_right {S} :
  S; Stmt.skip ~ S :=
  by
    intro s t
    apply Iff.intro
    { intro hseq
      cases hseq with
      | seq _ _ _ u _ hS hs =>
        cases hs
        assumption }
    { intro h
      apply BigStep.seq
      { assumption }
      { apply BigStep.skip } }

theorem BigStepEquiv.if_seq_while_skip {B S} :
  Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
  by
    intro s t
    apply Iff.intro
    { intro hif
      cases hif with
      | if_true _ _ _ _ _ hB hseq =>
        cases hseq with
        | seq _ _ _ u _ hS hT =>
          apply BigStep.while_true <;>
            assumption
      | if_false _ _ _ _ _ hB hskip =>
        cases hskip
        apply BigStep.while_false
        assumption }
    { intro hwhile
      cases hwhile with
      | while_true _ _ _ u _ hB hS hw =>
        apply BigStep.if_true
        exact hB
        apply BigStep.seq <;>
          assumption
      | while_false _ _ _ hB =>
        apply BigStep.if_false
        exact hB
        apply BigStep.skip }

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
    (hT : T₁ ~ T₂) :
  S₁; T₁ ~ S₂; T₂ :=
  by
    intro s t
    apply Iff.intro
    { intro hseq
      cases hseq with
      | seq _ _ _ u _ hS₁ hT₁ =>
        apply BigStep.seq
        { rw [BigStepEquiv] at hS
          rw [← hS]
          assumption }
        { rw [BigStepEquiv] at hT
          rw [← hT]
          assumption } }
    { intro hseq
      cases hseq with
      | seq _ _ _ u _ hS₂ hT₂ =>
        apply BigStep.seq
        { rw [BigStepEquiv] at hS
          rw [hS]
          assumption }
        { rw [BigStepEquiv] at hT
          rw [hT]
          assumption } }

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    intro s t
    apply Iff.intro
    { intro hif
      cases hif with
      | if_true _ _ _ _ _ hB hS₁ =>
        apply BigStep.if_true
        { assumption }
        { rw [BigStepEquiv] at hS
          rw [← hS]
          assumption }
      | if_false _ _ _ _ _ hB hT₁ =>
        apply BigStep.if_false
        { assumption }
        { rw [BigStepEquiv] at hT
          rw [← hT]
          assumption } }
    { intro hif
      cases hif with
      | if_true _ _ _ _ _ hB hS₂ =>
        apply BigStep.if_true
        { assumption }
        { rw [BigStepEquiv] at hS
          rw [hS]
          assumption }
      | if_false _ _ _ _ _ hB hT₂ =>
        apply BigStep.if_false
        { assumption }
        { rw [BigStepEquiv] at hT
          rw [hT]
          assumption } }


/- ## Question 3: An "Arity-Oriented" Language

In this problem, we'll look at a simple, typed functional language.

This language contains only three forms of expression:

* A function `fn n` of arity `n + 1` for any natural `n` (recall that the
  *arity* of a function is the number of arguments it takes)
* An "argument value" (i.e., a unitary value to which functions can be applied;
  this is like `()` in Lean)
* Function application

Letting `a` denote our universal argument value and `fnN` denote a function of
arity `N + 1`, we illustrate some example programs in this language:
* `a` (a value without any function application)
* `fn1 a a` (a fully applied function)
* `fn0` (a function value)
* `fn2 a` (a partially applied function)

We specify the abstract syntax of this language below: -/

inductive FnExp
  | fn  : Nat → FnExp
  | arg : FnExp
  | app : FnExp → FnExp → FnExp

/- In addition to syntax, we also define a *type system* for our language. Our
types are defined as an inductive datatype, just as our syntax is. We will have
two types of values:

* The type `argument`, which is equivalent to the unit type
* The type `function n` for any natural number `n`, which is the type of
  functions of arity `n + 1`

Notice the symmetry between types and expressions. (In this toy language, there
is a very direct correspondence; on the homework, you'll see a more complex
example.) -/

inductive FnType
  | function : Nat → FnType
  | argument : FnType

namespace FnExp

open FnType

/- We now define our language's statics by defining the *typing judgments* for
our language, represented by the `HasType` predicate. This predicate assigns a
type to every expression in our language. It also defines what constitutes a
*well-typed* expression; we call *ill-typed* any expression `e` for which there
exists no type `τ` such that `HasType e τ` holds. -/

inductive HasType : FnExp → FnType → Prop
  | fn {n} :
    HasType (fn n) (function n)
  | arg :
    HasType arg argument
  | appZero {f x} :
    HasType f (function 0) → HasType x argument → HasType (app f x) argument
  | appSucc {f x n} :
    HasType f (function (Nat.succ n)) → HasType x argument →
    HasType (app f x) (function n)

/- We define convenience notation for the `HasType` judgment, so we may write
expressions like `arg ∶ argument` for `HasType arg argument`.

Note: the `∶` symbol is not a colon! It is typed using `\:`. -/

scoped infix:50 " ∶ " => HasType

/- 3.1. Consider the following expression in our language (we use an informal
syntax for readability, writing function application in the traditional manner
instead of using `app`, and writing `fnN` for `fn N`):

`(fn3 arg) (fn0 arg)`

Write a typing derivation for the above expression. Your derivation should be
in tree form, just like in assignment 1. The difference here is that your typing
judgments are those specified by `HasType`.

Here are some useful ASCII symbols: `–`, `⊢`. -/

/-
–––––––––––––––––– fn ––––––––––– arg    –––––––––––––––––– fn ––––––––––– arg
⊢ fn3 : function 3  ⊢ arg : argument     ⊢ fn0 : function 0  ⊢ arg : argument
–––––––––––––––––––––––––––––– app_succ  –––––––––––––––––––––––––––––– app_zero
⊢ (fn3 arg) : function 2                 ⊢ (fn0 arg) : argument
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– app_succ
⊢ (fn3 arg) (fn0 arg) : function 1
-/

/- 3.2. Now complete the following Lean statement of this typing derivation by
filling in the appropriate type for the expression below and proving that it has
this type. (Hint: follow your proof tree!)

Note: there are tactics that will make this proof trivial. To get the most out
of it, though, you should try writing the specific terms, either using `apply`
or as a forward proof! -/

theorem tp_exercise : app (app (fn 3) arg) (app (fn 0) arg) ∶ function 1 :=
  HasType.appSucc (HasType.appSucc HasType.fn HasType.arg)
                  (HasType.appZero HasType.fn HasType.arg)

/- Next, we define our language's dynamics. Because we are defining a functional
language, our small-step semantics specifies transitions between *expressions*,
not states. As an example, consider the following example in a simple lambda
calculus-like language (we use `.` instead of `=>` to avoid ambiguity with `⇒`):

  (λ x f. f x) 0 (λ y. y)
  ⇒ (λ f. f 0) (λ y. y)
  ⇒ (λ y. y) 0
  ⇒ 0

The `⇒` predicate simply indicates what reduction step to take next in order to
evaluate a given expression. The same will apply to our language of `FnExp`s. -/

inductive Step : FnExp → FnExp → Prop
  | appArg {e e' x} : Step e e' → Step (app e x) (app e' x)
  | appZero {x}     : Step (app (fn 0) x) x
  | appSucc {x n}   : Step (app (fn (Nat.succ n)) x) (fn n)

-- We define the convenience notation `e ⇒ e'` for `Step e e'`
scoped infix:50 " ⇒ " => Step

/- Now that we have defined a statics and dynamics for our language, we must
ensure that they are mutually coherent. This is done by showing two key
properties that guarantee our language's *type safety*: *progress* and
*preservation*.

Intuitvely, progress guarantees that no well-typed expression gets "stuck"
during evaluation. More explicitly, every well-typed expression is either a
fully-evaluated value (like `3` or `true` or `[]` in Lean) or can take some step
according to our semantics. This connects our type system and our semantics in
the sense that it guarantees that, in our semantics, we've "accounted for" every
well-typed expression.

Preservation, on the other hand, says that a term preserves its original type
throughout evaluation. More formally, if an expression `e` has type `τ`, and `e`
steps to `e'`, then `e'` must also have type `τ`. (For instance, in Lean, if we
write an expression of type `Nat`, we don't want it to evaluate to a `String`!)

Together, these properties ensure that every well-typed term can be evaluated in
a well-typed manner. (There are, of course, further properties of the `FnExp`
language we could prove, such as *termination*: the property that every
expression will eventually evaluate to a value. Feel free to think about and
even try to prove some of these other properties if you're so inclined!)

We now prove the type safety of our `FnExp` language.

3.3. Prove that preservation holds for the `FnExp` language.

Hint: We recommend proceeding by rule induction on the step judgment. -/

theorem preservation {e e' : FnExp} {τ : FnType} :
  e ∶ τ → e ⇒ e' → e' ∶ τ :=
by
  intro htp hstep
  induction hstep generalizing τ with
  | @appArg f f' x h ih =>
    cases htp with
    | appZero hf hx =>
      apply HasType.appZero
      . exact ih hf
      . exact hx
    | @appSucc _ _ n hf hx =>
      apply HasType.appSucc
      . exact ih hf
      . exact hx
  | @appZero x =>
    cases htp with
    | appZero => assumption
    | appSucc hf hx => cases hf
  | @appSucc _ n =>
    cases htp with
    | appZero hf hx => cases hf
    | appSucc hf hx =>
      cases hf
      exact HasType.fn

/- Lastly, we prove progress. In order to do so, we need to define what a
"fully-evaluated expression" is in our language. For this purpose, we define a
predicate that specifies *values* in the `FnExp` language. Values are
expressions that are maximally reduced; they are the "final answers" we obtain
from our computations. (In Lean, for instance, `4`, `[]`, and `(λ x => x)` are
all values.) This definition enables us to state our progress theorem.

3.4. Prove that progress holds for the `FnExp` language. -/

inductive Value : FnExp → Prop
  | fn {n} : Value (fn n)
  | arg    : Value arg

theorem progress {e : FnExp} {τ : FnType} :
  e ∶ τ → Value e ∨ ∃ e', e ⇒ e' :=
by
  intro htp
  induction htp with
  | fn => exact Or.inl Value.fn
  | arg => exact Or.inl Value.arg
  | @appZero f x hf hx ihf ihx =>
    apply Or.inr
    cases ihf with
    | inl hval =>
      cases hval with
      | @fn n =>
        cases hf
        apply Exists.intro x
        apply Step.appZero
      | arg => cases hf
    | inr hstep =>
      cases hstep with | intro f' hf' =>
      apply Exists.intro (app f' x)
      exact Step.appArg hf'      
  | @appSucc f x n hf hx ihf ihx =>
    apply Or.inr
    cases ihf with
    | inl hval =>
      cases hf with
      | fn =>
        apply Exists.intro (fn n)
        exact Step.appSucc
      | appSucc => cases hval
    | inr hstep =>
      cases hstep with | intro f' hf' =>
      apply Exists.intro (app f' x)
      exact Step.appArg hf'

/- 3.5. Consider the alternative operational semantics `BadStep` below. Which
coherence property fails to hold if we use `BadStep` instead of `Step`? State
and prove the negation of this property using `BadStep`. -/

inductive BadStep : FnExp → FnExp → Prop
  | app_zero {x}   : BadStep (app (fn 0) x) x
  | app_succ {x n} : BadStep (app (fn (Nat.succ n)) x) (fn n)

-- Progress fails to hold
theorem negation_of_coherence_property : 
  ¬(∀ {e τ}, e ∶ τ → Value e ∨ ∃ e', BadStep e e') :=
by
  intro hneg
  -- Since `BadStep` doesn't step arguments, we just need to create a well-typed
  -- expression that has a non-value argument. This is the simplest:
  have htp : app (app (fn 1) arg) arg ∶ argument :=
    HasType.appZero (HasType.appSucc HasType.fn HasType.arg) HasType.arg
  -- By reductio hypothesis, it should be a value/step since it's well-typed...
  have hexp_step := hneg htp
  -- ...but it isn't/doesn't
  cases hexp_step with
  | inl hval =>  cases hval
  | inr hstep =>
    cases hstep with | intro e' he' =>
    cases he'

end FnExp

end LoVe
