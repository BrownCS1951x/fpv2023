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
  
noncomputable def Complex.toPolar (c : Complex) : Polar where 
  angle := Real.arctan (c.im / c.re) 
  magnitude := Real.sqrt (c.re^2 + c.im^2)

end Complex 

#check (5 : ℝ ) / 10
-- #reduce (5 : ℝ ) / 10

end new 