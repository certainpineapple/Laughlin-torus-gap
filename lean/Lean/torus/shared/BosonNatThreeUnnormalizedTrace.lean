import torus.shared.BosonNatThreeMatrixTrace
import torus.shared.BosonNatThreeAnnihilator

/-! Original, unnormalized Nat COM columns retain their full 3^n n! factor
when the actual charge-two cell integral is reduced to the charge-three vacuum.
No relative-label Gram or orthogonality assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeUnnormalizedTrace
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNormalizedNatSeeds
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance unnormalizedTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natThreeAnnihilator_descendant (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f =
      (Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ) • natThreeRemoval G theta p hp n R f := by
  have hr : Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (pow_pos (by norm_num) n) (by positivity)))
  have hc : (Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ) ≠ 0 := by exact_mod_cast hr
  have he : ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) =
      (Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ) • normalizedNatSeed 3 n p := by
    simp only [normalizedNatSeed, Nat.cast_ofNat, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [he]
  simp only [LinearMap.map_smulₛₗ,LinearMap.smul_apply,starRingEnd_apply]
  rw [natThreeAnnihilator_normalized G theta p hp n R]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem natThreeAnnihilator_descendant_cross_integrable (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip
      (natThreeAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f)
      (natThreeAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] r) g))
      (cellMeasure G 2) := by
  simp_rw [natThreeAnnihilator_descendant G theta p hp,
    natThreeAnnihilator_descendant G theta r hr,
    TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right]
  exact ((natThreeRemoval_cross_integrable G theta 2 p r hp hr n m f g).const_mul _).const_mul _

theorem natThreeAnnihilator_descendant_integral (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hpL : canonicalCOMLowerNat p=0) (hrL : canonicalCOMLowerNat r=0)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip
      (natThreeAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f)
      (natThreeAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] r) g)
        ∂cellMeasure G 2) =
      if n=m then (2/3:ℂ)*(3^n*(n.factorial:ℂ))*
        (∫ R, ip (natThreeRemoval G theta p hp 0 R f)
          (natThreeRemoval G theta r hr 0 R g) ∂cellMeasure G 3) else 0 := by
  simp_rw [natThreeAnnihilator_descendant G theta p hp,
    natThreeAnnihilator_descendant G theta r hr,
    TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right]
  rw [integral_const_mul,integral_const_mul,
    natThreeRemoval_com_integral G theta p r hp hr hpL hrL]
  by_cases h : n=m
  · subst m
    simp only [ite_true]
    simp only [Complex.star_def,Complex.conj_ofReal]
    have hs : (Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ)^2 = 3^n*(n.factorial:ℂ) := by
      exact_mod_cast Real.sq_sqrt (show 0≤(3:ℝ)^n*(n.factorial:ℝ) by positivity)
    calc
      _ = (2/3:ℂ)*(Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ)^2 *
        (∫ R, ip (natThreeRemoval G theta p hp 0 R f)
          (natThreeRemoval G theta r hr 0 R g) ∂cellMeasure G 3) := by ring
      _ = _ := by rw [hs]
  · simp only [h,ite_false,mul_zero]

/-- The full finite matrix trace of genuine unnormalized COM columns.
All off-relative-label entries remain until their COM levels are compared. -/
theorem finite_unnormalized_COM_matrix_trace {ι κ : Type*}
    (G : Geometry) (theta : Twist) (s : Finset ι) (t : Finset κ)
    (p : ι → Core ℕ ℂ) (r : κ → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 3) (hr : ∀ j, (r j).IsHomogeneous 3)
    (hpL : ∀ i, canonicalCOMLowerNat (p i)=0)
    (hrL : ∀ j, canonicalCOMLowerNat (r j)=0)
    (n : ι → ℕ) (m : κ → ℕ) (C : ι → κ → ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i ∈ s, ∑ j ∈ t, C i j * ip
      (natThreeAnnihilator G theta R
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n i] (p i)) f)
      (natThreeAnnihilator G theta R
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m j] (r j)) g)
        ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i ∈ s, ∑ j ∈ t, if n i=m j then
      (3^(n i)*((n i).factorial:ℂ))*C i j *
        (∫ R, ip (natThreeRemoval G theta (p i) (hp i) 0 R f)
          (natThreeRemoval G theta (r j) (hr j) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  have hi (i : ι) (j : κ) :=
    (natThreeAnnihilator_descendant_cross_integrable G theta (p i) (r j)
      (hp i) (hr j) (n i) (m j) f g).const_mul (C i j)
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum t (fun j _ => hi i j))]
  simp_rw [integral_finsetSum t (fun j _ => hi _ j),integral_const_mul,
    natThreeAnnihilator_descendant_integral G theta _ _ (hp _) (hr _) (hpL _) (hrL _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  apply Finset.sum_congr rfl
  intro j hjt
  split_ifs <;> ring

end TorusLean.Shared.BosonNatThreeUnnormalizedTrace
