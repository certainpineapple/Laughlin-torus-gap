import torus.boson.FiniteOccupationCCR
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPairNormalOrder
open TorusLean.Boson

/-- Exact CCR reordering on the original finite polynomial core: the four
single contractions have positive sign, and both double contractions remain.
No positivity or finite-particle certificate is a hypothesis. -/
theorem annihilate_pair_create_pair {ι : Type*} [DecidableEq ι]
    (i j k l : ι) (f : Core ι ℂ) :
    annihilate i (annihilate j (create k (create l f))) =
      create k (create l (annihilate i (annihilate j f))) +
      (if j = k then create l (annihilate i f) else 0) +
      (if j = l then create k (annihilate i f) else 0) +
      (if i = k then create l (annihilate j f) else 0) +
      (if i = l then create k (annihilate j f) else 0) +
      (if j = k ∧ i = l then f else 0) +
      (if j = l ∧ i = k then f else 0) := by
  classical
  by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    by_cases hik : i = k <;> by_cases hil : i = l <;>
    simp_all [annihilate, create, MvPolynomial.pderiv_mul, Pi.single_apply] <;> ring


#print axioms annihilate_pair_create_pair
end TorusLean.Shared.BosonPairNormalOrder
