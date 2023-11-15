import AutograderLib
import LoVe.Lectures.LoVe14_RationalAndRealNumbers_Demo
import Mathlib.Data.Nat.Parity

/- # FPV Homework 9: Rationals, Reals, Quotients

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/

set_option maxHeartbeats 50000

namespace LoVe

/-

## Question 1 (4 points): Cauchy Sequences

1.1 (4 points). In the demo, we sorry'ed the proof that the sum of two Cauchy
sequences is Cauchy. Prove this!

Warning: Due to a Lean bug, if you have errors in your proof, Lean may time out
instead of properly identifying them. If this happens, the timeout error will
usually occur on the line on which you've made the error and will say something
about `isDefEq` timing out.

Hint: depending on how you approach this, you might want to do a long calc-mode
proof. Recall that calc-mode proofs look as follows:
-/

lemma quarter_pos {x : ℚ} (hx : 0 < x) : 0 < x / 4 :=
by
  have hx2 : 0 < x / 2 := half_pos hx
  calc 0 < (x / 2) / 2 := half_pos hx2
       _ = x / 4 := by ring

@[autograded 4]
lemma sum_is_cauchy (f g : ℕ → ℚ) (hf : IsCauchySeq f) (hg : IsCauchySeq g) :
  IsCauchySeq (λ n => f n + g n) :=
  sorry

/-
## Question 2 (4 points): Operations on the Reals

2.1 (3 points). In the demo, we proved `add_comm` on the reals by first proving
it for Cauchy sequences and then lifting this proof. Follow this same procedure
to prove a lemma `zero_add` that says that `0 + x = x` for any real number `x`.
State the lemma yourself (along with any helper lemmas you may need -- we suggest
defining something like `add_def`, proved by `rfl`)! -/

open LoVe.CauchySeq

-- Write your answer to 2.1 here


/- 2.2 (1 point). Every rational number corresponds to a real number. Define
this coercion. -/

instance ratRealCoe : Coe ℚ Real :=
{ coe :=
  sorry }

/- ## Question 3 (6 points): Quotients in General

In this problem we'll take a weird quotient of ℕ.

The following lemmas may be useful: -/

#check even_zero
#check Nat.not_even_one

/- 3.1 (2 points). Define a setoid structure on ℕ using the equivalence relation
where `x ≈ y` if and only if `x` and `y` are both even or both odd.

E.g. `0 ≈ 2`, `1 ≈ 5`, but `¬ 4 ≈ 5`. -/

instance eqv : Setoid ℕ := {
  r := sorry,
  iseqv := sorry
}


/- Now we'll define the quotient of ℕ by this relation. There are two elements
of the quotient: -/

def EONat := Quotient eqv

def e : EONat := ⟦0⟧
def o : EONat := ⟦1⟧

/- 3.2 (2 points). Prove that these are the only two elements of `EONat`. -/
@[autograded 2] lemma e_or_o (x : EONat) : x = e ∨ x = o :=
  sorry

/- 3.3 (2 points). Lift the addition function on ℕ to `EONat`.

What does the "addition table" for `EONat` look like? That is, what are `e+e`,
`o+o`, `e+o`, and `o+e`? State and prove two of these identities. -/

def add : EONat → EONat → EONat :=
  sorry


end LoVe
