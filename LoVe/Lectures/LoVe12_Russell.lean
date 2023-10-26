/- ## Russell's Paradox in Type Theory

This section draws in part on Ulrik Buchholtz's presentation of this material:
https://github.com/martinescardo/HoTTEST-Summer-School/tree/main/Agda/Auxiliary

You may be familiar with *Russell's paradox*, a classic set-theoretic result.
It shows that so-called "naïve set theory" is inconsistent because such a set
theory admits the set `R = {x | x ∉ x}` of all sets that do not contain
themselves, which one can show satisfies `R ∈ R ↔ R ∉ R` -- a contradiction.
We'll show here that, without type universes, an analogous paradox arises in
dependent type theory. This result was first shown by Coquand.

Note: a stronger result, known as *Girard's paradox*, holds for a broader class
of type theories, but its proof is highly technical.
-/

namespace Russell

/-
We first define a couple of types we've been working with in `Prop` at the
`Type` level. (The proof won't go through in `Prop` due to its prohibition of
large elimination. After seeing how the proof goes, you might think about why
this is the case!)

First, recall that `Empty` is a type with no terms, defined as:
  
  inductive Empty : Type

It is the `Type` analogue of `False : Prop`.

Recall also that `¬P : Prop` is notation for `P → False`. Since `Empty` is
analogous to `False`, it follows that `Not` below is the `Type`-level analogue
of `¬`.
-/

def Not (α : Type) := α → Empty

/-
Next, we define the identity `Type` analogous to `Eq : ∀ {α}, α → α → Prop`, the
equality predicate we use when we write the `=` sign. We define the custom
notation `≡` for our equality `Type` to avoid confusion with the `Prop`.

Just as with `Eq`, the type `EqType x y` (aka `x ≡ y`) is inhabited just when
`x` and `y` are (provably) equal.
-/

inductive EqType {α : Type} : α → α → Type
  | refl {a : α} : EqType a a

infix:50 " ≡ "  => EqType

/-
So far, everything we've done is completely permitted by Lean's type theory. Now
we make our "illegal" declaration that, in essence, encodes the idea that we
have `Type u : Type u` for some `u`.

Given a function `f : Type → Type` (say `f := λ (X : Type) => X × X`), the type
`∀ X, f X` has type `Type 1`. In general, `∀` produces a type one level higher
in the type hierarchy than its arguments.

If we collapsed the universe hierarchy, though, `∀ X, f X` would simply have
type `Type`.

Lean won't allow this declaration, of course (we're about to show it's
unsound!), so we've written below how the declaration would look in Lean's
syntax, then faked the important parts using `axiom`s.

Don't worry too much about how the fake declarations are implemented; just
pretend that the inductive definition below were accepted by Lean.
-/


-- inductive V : Type
-- | sup : ∀ (X : Type), (X → V) → V


section
--------------------------------------------------------------------------------
/- This axiomatizes the salient parts of what the inductive definition above
would have done. You don't need to worry about these details (unless you're
curious); in fact, we recommend collapsing this section using the arrow that
appears if you hover to the left of `section` above. -/

universe u
axiom V : Type

axiom V.sup : (X : Type) → (X → V) → V

axiom V.recConst :
  {motive : Sort u} →
  ((X : Type) → (X → V) → motive) →
  (t : V) →
  motive

axiom V.recConst_spec {motive : Sort u}
  (p : (X : Type) → (X → V) → motive)
  (X : Type)
  (f : X → V) :
  V.recConst p (V.sup X f) = p X f

syntax "rewrite_recursor_term" term : term
syntax "rewrite_recursor_term_rev" term : term
macro_rules
| `(rewrite_recursor_term $t) => `(cast (V.recConst_spec _ _ _) $t)
| `(rewrite_recursor_term_rev $t) =>
  `(cast (Eq.symm $ V.recConst_spec _ _ _) $t)
--------------------------------------------------------------------------------
end

/-
We're going to think of terms of type `V` as representing sets: roughly
speaking, `V.sup X f : V` corresponds to the set given by `{f x | x : X}`.

To encode this notion of sethood, we declare below a membership predicate on
such sets. The type `Mem elt set` (or `elt ∈ set`), where `set = V.sup X f`, is
inhabited just when there is some `x' : X` such that `elt = f x'`. Notice that
this matches our set representation above.

An element of `Mem elt set` consists of a *dependent pair* `⟨x', p⟩`, where `p`
is a proof that `elt = f x'` (notice how the type of `p` depends on `x'`).

The commented declaration below represents how we would define `Mem` if we had
defined `V` using the standard `inductive` declaration we gave before. Since we
couldn't actually make such a declaration and used `axiom` trickery instead,
we've had to provide a "lower-level" definition of `Mem`, but it is equivalent
to the commented pattern-matching one.
-/

/-
def Mem : V → V → Type
| elt, V.sup X f => (x' : X) × (elt ≡ f x')
-/
def Mem (elt : V) (set : V) : Type :=
  set.recConst λ X f => (x' : X) × (elt ≡ f x')

/-
Under this notion of membership, we can think of a term `V.sup X f : V` as
representing a set given by `{f x | x : X}`.
-/

-- We write `elt ∈ set` for `Mem elt set` and `elt ∉ set` for `Not (elt ∈ set)`
infix:50 " ∈ " => Mem
notation:50 x:50 " ∉ " y:50 => Not (Mem x y)

/-
We define our Russell set: the set consisting of all sets `v` such that `v ∉ v`.
We define this by taking our indexing type `X` to be the dependent pair type
`(v : V) × (v ∉ v)` (i.e, the subtype of all sets that do not contain
themselves), then taking our function on that type to be the projection
in the first component, extracting `v`.

This is the step where we exploit the fact that `V` lives in `Type` (and not, as
it should, `Type 1`). If `V : Type 1`, then we could not take `X` to be
`(v : V) × (v ∉ v)`, since `(v : V) × (v ∉ v)` would, like `v`, have type
`Type 1`, while `X` must have type `Type`. Note the similarity to the set-
theoretic version of Russell's paradox: this is the same sort of problematic
self-reference that causes trouble in naïve set theory.
-/
noncomputable def R : V := V.sup ((v : V) × (v ∉ v)) -- X
                                 (λ ⟨v, _⟩ => v)     -- f

/-
We show the two directions of the bi-implication that characterizes `R`:
`v ∈ R` if and only if `v ∉ v`. The `rewrite_recursor_term` macros allow Lean to
recognize our axiomatized definitions (they're not doing anything sneaky!).
-/

def not_mem_self_of_mem_R (v : V) : v ∈ R → v ∉ v :=
  λ (hvR : v ∈ R) =>
    -- Recall that `v ∈ R` is notation for `(x' : X) × (x'.1 ≡ v)` where (by our
    -- definition of `R`) we have `X = (v' : V) × (v' ∉ v')`. We unpack our
    -- "generator" value `⟨v', hnvv⟩ : (v' : V) × (v' ∉ v')`; via the proof
    -- `refl : v' ≡ v`, the proof `hnvv` has type `v ∉ v`, which is the type
    -- we're looking for.
    match rewrite_recursor_term hvR with
    | ⟨⟨_, hnvv⟩, .refl⟩ => hnvv

def mem_R_of_not_mem_self (v : V) : v ∉ v → v ∈ R :=
  λ hvv => rewrite_recursor_term_rev ⟨⟨v, hvv⟩, .refl⟩

/-
Now we derive two contradictory statements: `R ∉ R` and `R ∈ R`. Using these, we
can show `Empty` (i.e., falsehood) to be inhabited (i.e., proved)!
-/

def R_not_mem_R : R ∉ R :=
  λ hnRR => not_mem_self_of_mem_R R hnRR hnRR

noncomputable def R_mem_R : R ∈ R :=
  mem_R_of_not_mem_self R R_not_mem_R

noncomputable def uh_oh : Empty :=
  R_not_mem_R R_mem_R

end Russell
