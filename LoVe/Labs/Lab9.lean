import LoVe.Lectures.LoVe14_RationalAndRealNumbers_Demo


/- # FPV Lab 9: Rational and Real Numbers

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option autoImplicit false

namespace LoVe


/- ## Question 1: Rationals

1.1. Prove the following theorem.

Hints:

* Start with case distinctions on `a` and `b`.

* When the goal starts getting complicated, use `simp at *` to clean it up. -/

theorem Fraction.ext (a b : Fraction) (hnum : Fraction.num a = Fraction.num b)
    (hdenom : Fraction.denom a = Fraction.denom b) :
  a = b :=
  sorry

/- 1.2. Extending the `Fraction.Mul` instance from the lecture, declare
`Fraction` as an instance of `Semigroup`.

Hint: Use the theorem `Fraction.ext` above, and possibly `Fraction.mul_num` and
`Fraction.mul_denom`. -/

#check Fraction.ext
#check Fraction.mul_num
#check Fraction.mul_denom

instance Fraction.Semigroup : Semigroup Fraction :=
  { Fraction.Mul with
    mul_assoc :=
      sorry
  }

/- 1.3. Extending the `Rat.Mul` instance from the lecture, declare `Rat` as an
instance of `Semigroup`. -/

instance Rat.Semigroup : Semigroup Rat :=
  { Rat.Mul with
    mul_assoc :=
      sorry
  }

end LoVe
