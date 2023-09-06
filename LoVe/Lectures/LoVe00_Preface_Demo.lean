import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith

/-! # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS, Idris


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the odd-order theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL);
* the Liquid Tensor Experiment (in Lean)

Computer science:

* hardware
* operating systems
* programming language theory
* compilers
* security


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura (Microsoft
Research) since 2012.

Its mathematical library, `mathlib`, is developed by a user community.

We are using Lean 4, a recent version. We use its basic libraries, `mathlib`, and
`LoVelib`. Lean is a research project.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* wonderful user community.


## This Course

### Web Site

    https://BrownCS1951x.github.io 


### Repository (Demos, Exercises, Homework)

    https://github.com/BrownCS1951x/fpv2023

The file you are currently looking at is a demo. 
For each chapter of the Hitchhiker's Guide, there will be approximately
one demo, one exercise sheet, and one homework.

* Demos will be covered in class. These are "lecture notes."
  We'll post skeletons of the demos before class, and completed demos after class.

* Exercises are for weekly lab sessions run by the TAs.

* Homeworks are for you to do on your own, and submit via Gradescope.


### The Hitchhiker's Guide to Logical Verification

    https://cs.brown.edu/courses/cs1951x/static_files/main.pdf

The lecture notes consist of a preface and 14 chapters. They cover the same
material as the corresponding lectures but with more details. Sometimes there
will not be enough time to cover everything in class, so reading the lecture
notes will be necessary.

Download this version, not others that you might find online!


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* familiarize yourselves with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our vehicle, not an end in itself.

-/

open Nat 

-- here's a proof that there are infinitely many primes, as a mathematical theorem

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by 

  intro M 
  let F := M ! + 1
  let q := minFac F 
  use q 

  have qPrime : Nat.Prime q 
  { refine' minFac_prime _
    have hn : M ! > 0 := factorial_pos M 
    linarith }

  apply And.intro 

  { by_contra hqM
    have h1 : q ∣ M ! + 1 := minFac_dvd F
    have hqM2 : q ≤ M := by linarith
    have hqM3 : q ∣ M ! := Iff.mpr (Prime.dvd_factorial qPrime) hqM2
    have hq1 : q ∣ 1 := Iff.mp (Nat.dvd_add_right hqM3) h1
    apply Nat.Prime.not_dvd_one qPrime hq1
  }
  { assumption }
  done



-- but really, this is a proof about a *program* caled `biggerPrime`!

def biggerPrime (M : ℕ) : ℕ := Nat.minFac (M ! + 1)

#eval biggerPrime 7

theorem biggerPrimeIsPrime : ∀ N, Nat.Prime (biggerPrime N) := by 
  intro M
  refine' minFac_prime _
  have hn : M ! > 0 := factorial_pos M 
  linarith 
  done

theorem biggerPrimeIsBigger : ∀ N, biggerPrime N ≥ N := by 
  intro M
  by_contra hqM
  have h1 : (biggerPrime M) ∣ M ! + 1 := minFac_dvd _
  have hqM2 : biggerPrime M ≤ M := by linarith
  have hqM3 : biggerPrime M ∣ M ! :=
    Iff.mpr (Prime.dvd_factorial (biggerPrimeIsPrime _)) hqM2
  have hq1 : biggerPrime M ∣ 1 := Iff.mp (Nat.dvd_add_right hqM3) h1
  apply Nat.Prime.not_dvd_one (biggerPrimeIsPrime _) hq1
  done


-- we can use our verified program to prove our original theorem
theorem infinitude_of_primes2 : ∀ N, ∃ p ≥ N, Nat.Prime p := by 
  intro N 
  use biggerPrime N 
  apply And.intro 
  { exact biggerPrimeIsBigger _ }
  { exact biggerPrimeIsPrime _ }
  done 


