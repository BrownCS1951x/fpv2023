import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

namespace new

structure Complex : Type where 
  re : ℝ 
  im : ℝ 

def i : Complex where 
  re := 0
  im := 1

structure Polar : Type where 
  angle : ℝ  
  magnitude : ℝ 
  -- mag_nneg : magnitude ≥ 0

namespace Complex 


def zero : Complex where 
  re := 0
  im := 0

def add (a b : Complex) : Complex where 
  re := a.re + b.re 
  im := a.im + b.im 

/-

(x + iy)(z + iw) = (xz - yw) + (zy + xw)i 

-/

def mul (a b : Complex) : Complex where 
  re := a.re * b.re - a.im * b.im 
  im := a.im * b.re + a.re * b.im

def neg (a : Complex) : Complex where 
  re := -a.re 
  im := -a.im

instance : CommRing Complex where 
  add := Complex.add 
  mul := Complex.mul 
  neg := Complex.neg 
  zero := Complex.zero 
  one := {re := 1, im := 0}
  add_assoc := by 
    intro a b c 
    simp [.+.]
    simp [Complex.add]
    ring_nf


example (a b c : Complex) : a * 1 * b + c = c + b*a - 0*(a + b) := by 
  ring
  
@[norm_cast]
lemma coe_eq_zero (z : ℤ) : (z : Complex) = 0 ↔ z = 0 :=
  sorry

example (a b c : ℤ) : (a : Complex) - a = 0 := by 
  norm_cast
  rw [coe_eq_zero]
  simp


end Complex 


noncomputable def Complex.toPolar (c : Complex) : Polar where 
  angle := Real.arctan (c.im / c.re) 
  magnitude := Real.sqrt (c.re^2 + c.im^2)

-- cos angle = re / magnitude

noncomputable def Polar.toComplex (p : Polar) : Complex where 
  re := p.magnitude * Real.cos p.angle
  im := p.magnitude * Real.sin p.angle

theorem to_and_from (p : Polar) (hpmag : p.magnitude > 0)
    (hpangle1 : -( Real.pi / 2) < p.angle)
    (hpangle2 : p.angle < Real.pi / 2) : p.toComplex.toPolar = p := by 
  cases' p with pangle pmag
  simp at hpmag 
  simp [Complex.toPolar, Polar.toComplex] 
  constructor 
  { rw [mul_div_mul_left]
    rw [← Real.tan_eq_sin_div_cos]
    rw [Real.arctan_tan]
    all_goals aesop }
  { suffices : (pmag * Real.cos pangle)^2 + (pmag * Real.sin pangle)^2 = pmag^2
    rw [this]
    rw [Real.sqrt_sq] 
    linarith
    have h : (Real.sin pangle)^2 + (Real.cos pangle)^2 = 1 :=
      Real.sin_sq_add_cos_sq pangle
    linear_combination pmag ^ 2 * h }

#check (5 : ℝ ) / 10
-- #reduce (5 : ℝ ) / 10

def reals : Set Complex := 
{ c : Complex | c.im = 0}

end new 