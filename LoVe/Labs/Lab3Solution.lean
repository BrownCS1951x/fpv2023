import LoVe.LoVelib

/- # FPV Lab 3: Forward Proofs -/

set_option autoImplicit false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume hg : a → b → c
  assume hb : b
  assume ha : a
  show c from
    hg ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha'

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume hg : a → b → c
  assume ha : a
  assume hf : a → c
  assume hb : b
  have hc : c :=
    hf ha
  show c from
    hc

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  have hb : b :=
    hab ha
  show False from
    hnb hb

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume hpq : ∀x, p x ∧ q x
     have hp : ∀x, p x :=
       fix x : α
       And.left (hpq x)
     have hq : ∀x, q x :=
       fix x : α
       And.right (hpq x)
     show (∀x, p x) ∧ (∀x, q x) from
       And.intro hp hq)
    (assume hpq : (∀x, p x) ∧ (∀x, q x)
     have hp : ∀x, p x :=
       And.left hpq
     have hq : ∀x, q x :=
       And.right hpq
     assume x : α
     show p x ∧ q x from
       And.intro (hp x) (hq x))

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hpxy : ∃x, ∀y, p x y
  fix b : α
  show ∃x, p x b from
    Exists.elim hpxy
      (fix a : α
       assume hpay : ∀y, p a y
       show ∃x, p x b from
         Exists.intro a (hpay b))


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
calc
  (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by
      simp only [add_mul, mul_add]
      ac_rfl
  _ = a * a + a * b + b * a + b * b :=
    by
      simp only [add_mul, mul_add]
      ac_rfl
  _ = a * a + a * b + a * b + b * b :=
    by simp only [mul_comm]
  _ = a * a + 2 * a * b + b * b :=
    by simp only [Nat.two_mul, add_mul, add_assoc]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations.

You can use tactical proofs (some copy/pasting might be in order!) to prove each
of your `have` steps.) You'll also want to use a tactical proof to `show` your
final goal. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by
      simp only [add_mul, mul_add]
      ac_rfl
  have h2 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
    by
      simp only [add_mul, mul_add]
      ac_rfl
  have h3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by simp only [mul_comm]
  have h4 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by simp only [Nat.two_mul, add_mul, add_assoc]
  show _ from
    by
      rw [h1]
      rw [h2]
      rw [h3]
      rw [h4]


/- ## Question 3: One-Point Rules

3.1. Prove that the following wrong formulation of the one-point rule for `∀` is
inconsistent, using a structured proof.

How should this rule be modified to produce the correct one-point rule? -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  by
    have hwrong : (∀x, x = 0 ∧ True) ↔ True :=
      All.one_point_wrong 0 (fun _ ↦ True)
    simp at hwrong
    have hone_eq_zero : 1 = 0 :=
      hwrong 1
    cases hone_eq_zero

/- 3.2. Prove that the following wrong formulation of the one-point rule for `∃`
is inconsistent, using a structured proof.

How should this rule be modified to produce the correct one-point rule? -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  by
    have hwrong : (∃x, x ≠ 0) ↔ False :=
      Exists.one_point_wrong 0 (fun _ ↦ False)
    simp at hwrong
    have hone_eq_zero : 1 = 0 :=
      hwrong 1
    cases hone_eq_zero

end LoVe
