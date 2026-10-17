import torus.geometry.IntegerLattice
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# ZLattice summability on the actual physical period image

This consumes the derived discrete integer lattice, not a discretely typed
coordinate surrogate. The inverse-power estimate is for each fixed legal
geometry. It does not prove shape-uniform packing, magnetic Gaussian image
convergence, or differentiated-series convergence.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

noncomputable section

def periodEquivIntegerLattice (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    (ℤ × ℤ) ≃ integerLattice omega1 omega2 :=
  Equiv.ofBijective
    (fun p : ℤ × ℤ => (⟨latticePeriod omega1 omega2 p,
      (integerLattice_mem_iff omega1 omega2 _).mpr ⟨p, rfl⟩⟩ : integerLattice omega1 omega2))
    ⟨by
      intro p q hpq
      apply latticePeriod_injective M hM omega1 omega2 harea
      exact congrArg (fun x : integerLattice omega1 omega2 => (x : ℂ)) hpq,
     by
      rintro ⟨z, hz⟩
      obtain ⟨p, hp⟩ := (integerLattice_mem_iff omega1 omega2 z).mp hz
      exact ⟨p, Subtype.ext hp⟩⟩

theorem periodEquivIntegerLattice_val (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) (p : ℤ × ℤ) :
    (periodEquivIntegerLattice M hM omega1 omega2 harea p : ℂ) =
      latticePeriod omega1 omega2 p := rfl

theorem integerLattice_summable_inv_pow (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (n : ℕ) (hn : 2 < n) (z : ℂ) :
    Summable (fun lambda : integerLattice omega1 omega2 => ‖(lambda : ℂ) - z‖⁻¹ ^ n) := by
  letI := integerLattice_discrete M hM omega1 omega2 harea
  exact ZLattice.summable_norm_sub_inv_pow (integerLattice omega1 omega2) n
    (by rw [integerLattice_rank_two M hM omega1 omega2 harea]; exact hn) z

theorem latticePeriod_summable_inv_pow (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (n : ℕ) (hn : 2 < n) (z : ℂ) :
    Summable (fun p : ℤ × ℤ => ‖latticePeriod omega1 omega2 p - z‖⁻¹ ^ n) := by
  have hs := integerLattice_summable_inv_pow M hM omega1 omega2 harea n hn z
  have h := (periodEquivIntegerLattice M hM omega1 omega2 harea).summable_iff.mpr hs
  simpa only [Function.comp_def, periodEquivIntegerLattice_val] using h

#print axioms periodEquivIntegerLattice_val
#print axioms integerLattice_summable_inv_pow
#print axioms latticePeriod_summable_inv_pow

end

end TorusLean.Geometry
