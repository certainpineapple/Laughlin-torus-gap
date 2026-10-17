import torus.geometry.LatticePhase

/-!
# Integer period-map injectivity from actual positive magnetic area

Only the legal physical inputs occur: natural positive flux, the two complex
periods, and `Im(conj omega1*omega2)=pi*M`. Discreteness and positive systole
are not supplied as assumptions. This module supplies the elementary
coordinate/image bridge needed to interpret the actual image sums.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

theorem latticeArea_pos (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    0 < latticeArea omega1 omega2 := by
  rw [harea]
  exact mul_pos Real.pi_pos (Nat.cast_pos.mpr hM)

theorem latticePeriod_sub (omega1 omega2 : ℂ) (p q : ℤ × ℤ) :
    latticePeriod omega1 omega2 (p - q) =
      latticePeriod omega1 omega2 p - latticePeriod omega1 omega2 q := by
  simp only [latticePeriod, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

theorem latticePeriod_eq_zero_iff (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) (p : ℤ × ℤ) :
    latticePeriod omega1 omega2 p = 0 ↔ p = 0 := by
  have hA : latticeArea omega1 omega2 ≠ 0 :=
    ne_of_gt (latticeArea_pos M hM omega1 omega2 harea)
  constructor
  · intro hp
    have h1 := lattice_symplectic omega1 omega2 p (0, 1)
    have h2 := lattice_symplectic omega1 omega2 p (1, 0)
    simp only [hp, zero_mul, Complex.zero_im, mul_zero, mul_one, zero_sub, sub_zero,
      Int.cast_neg, Int.cast_one, Int.cast_zero] at h1 h2
    have hp1 : (p.1 : ℝ) = 0 := by
      have hz := (mul_eq_zero.mp h1.symm).resolve_right hA
      exact neg_eq_zero.mp hz
    have hp2 : (p.2 : ℝ) = 0 :=
      (mul_eq_zero.mp h2.symm).resolve_right hA
    apply Prod.ext
    · exact Int.cast_eq_zero.mp hp1
    · exact Int.cast_eq_zero.mp hp2
  · intro hp
    rw [hp]
    exact latticePeriod_zero omega1 omega2

theorem latticePeriod_injective (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    Function.Injective (latticePeriod omega1 omega2) := by
  intro p q hpq
  have hz : latticePeriod omega1 omega2 (p - q) = 0 := by
    rw [latticePeriod_sub, hpq, sub_self]
  exact sub_eq_zero.mp ((latticePeriod_eq_zero_iff M hM omega1 omega2 harea (p - q)).mp hz)

/-- Integer-coordinate enumeration is a bijection onto the actual lattice
image, rather than a duplicate sum over a degenerate parameterization. -/
def latticePeriodEquivImage (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    (ℤ × ℤ) ≃ Set.range (latticePeriod omega1 omega2) :=
  Equiv.ofInjective (latticePeriod omega1 omega2)
    (latticePeriod_injective M hM omega1 omega2 harea)

#print axioms latticeArea_pos
#print axioms latticePeriod_sub
#print axioms latticePeriod_eq_zero_iff
#print axioms latticePeriod_injective

end

end TorusLean.Geometry
