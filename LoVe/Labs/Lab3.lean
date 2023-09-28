import LoVe.LoVelib

/- # FPV Lab 3: Forward Proofs -/

set_option autoImplicit false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  sorry

theorem K (a b : Prop) :
  a → b → b :=
  sorry

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  sorry

theorem proj_fst (a : Prop) :
  a → a → a :=
  sorry

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  sorry

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  sorry

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  sorry

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  sorry

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  sorry


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `rw`, `simp` and
`ac_rfl` and some of the theorems listed below: -/

#check mul_add
#check add_mul
#check add_comm
#check add_assoc
#check mul_comm
#check mul_assoc
#check Nat.two_mul

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations.

You can use tactical proofs (some copy/pasting might be in order!) to prove each
of your `have` steps.) You'll also want to use a tactical proof to `show` your
final goal. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry


/- ## Question 3: One-Point Rules

3.1. Prove that the following wrong formulation of the one-point rule for `∀` is
inconsistent, using a structured proof.

How should this rule be modified to produce the correct one-point rule? -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  sorry

/- 3.2. Prove that the following wrong formulation of the one-point rule for `∃`
is inconsistent, using a structured proof.

How should this rule be modified to produce the correct one-point rule? -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  sorry

end LoVe
