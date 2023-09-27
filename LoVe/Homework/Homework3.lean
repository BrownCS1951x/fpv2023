import LoVe.LoVelib
import AutograderLib

/- # FPV Homework 3: Forward Proofs

In this homework, you'll practice writing forward proofs.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (1 point). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

@[autograded 1] theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

@[autograded 2] theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry

/-
1.3 (2 points). The following lemma will be helpful for part 4.
Prove it! For an extra challenge, prove it without using classical logic -- 
no `Classical.em` or `Classical.byContradiction`. 
-/

@[autograded 2]
lemma not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P) := 
 sorry 


example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
  not_iff_not_self Q


/- 1.4 (1 point). In a certain faraway village, there is only one barber for
the whole town. He shaves all those who do not shave themselves. Does the barber
shave himself? 

Provide a structured proof showing that this premise implies `False`.
-/



section
  @[autograded 1] theorem false_of_barber
    (Person : Type)
    (shaves : Person → Person → Prop)
    (barber : Person)
    (h : ∀ x, shaves barber x ↔ ¬ shaves x x)
    : False :=
    sorry
end



/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

@[autograded 3] theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  sorry



/-! ## Question 3 (2 points): Calc Mode
Use `calc` mode to prove that the difference of squares formula holds on the
integers. (In this particular problem, working on the integers is necessary, but
in practice not much different from working on ℕ.)

You might find some of the following lemmas useful!
-/
#check mul_sub
#check sub_add_eq_sub_sub
#check sub_add
#check add_sub_assoc
#check sub_self
#check mul_comm
#check add_mul
#check add_zero
#check zero_add

@[autograded 2] lemma difference_of_squares (a b : ℤ) :
  (a + b) * (a - b) = a * a - b * b :=
  sorry


end LoVe
