import torus.shared.BosonNatFourMatrixLift
import torus.shared.BosonNatFourAnnihilator

/-! Original, unnormalized Nat COM columns retain their full 4^n n! factor
when the actual charge-two cell integral is reduced to the charge-four vacuum.
No relative-label Gram or orthogonality assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourUnnormalizedTrace
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonNormalizedNatSeeds
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance unnormalizedTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natFourAnnihilator_descendant (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f =
      (Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ) • natFourRemoval G theta p hp n R f := by
  have hr : Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (pow_pos (by norm_num) n) (by positivity)))
  have hc : (Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ) ≠ 0 := by exact_mod_cast hr
  have he : ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) =
      (Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ) • normalizedNatSeed 4 n p := by
    simp only [normalizedNatSeed, Nat.cast_ofNat, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [he]
  simp only [LinearMap.map_smulₛₗ,LinearMap.smul_apply,starRingEnd_apply]
  rw [natFourAnnihilator_normalized G theta p hp n R]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem natFourAnnihilator_descendant_cross_integrable (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip
      (natFourAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f)
      (natFourAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] r) g))
      (cellMeasure G 2) := by
  simp_rw [natFourAnnihilator_descendant G theta p hp,
    natFourAnnihilator_descendant G theta r hr,
    TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right]
  exact ((natFourRemoval_cross_integrable G theta 2 p r hp hr n m f g).const_mul _).const_mul _

theorem natFourAnnihilator_descendant_integral (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4)
    (hpL : canonicalCOMLowerNat p=0) (hrL : canonicalCOMLowerNat r=0)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip
      (natFourAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) f)
      (natFourAnnihilator G theta R ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] r) g)
        ∂cellMeasure G 2) =
      if n=m then (2/4:ℂ)*(4^n*(n.factorial:ℂ))*
        (∫ R, ip (natFourRemoval G theta p hp 0 R f)
          (natFourRemoval G theta r hr 0 R g) ∂cellMeasure G 4) else 0 := by
  simp_rw [natFourAnnihilator_descendant G theta p hp,
    natFourAnnihilator_descendant G theta r hr,
    TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right]
  rw [integral_const_mul,integral_const_mul,
    natFourRemoval_com_integral G theta p r hp hr hpL hrL]
  by_cases h : n=m
  · subst m
    simp only [ite_true]
    simp only [Complex.star_def,Complex.conj_ofReal]
    have hs : (Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ)^2 = 4^n*(n.factorial:ℂ) := by
      exact_mod_cast Real.sq_sqrt (show 0≤(4:ℝ)^n*(n.factorial:ℝ) by positivity)
    calc
      _ = (2/4:ℂ)*(Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ)^2 *
        (∫ R, ip (natFourRemoval G theta p hp 0 R f)
          (natFourRemoval G theta r hr 0 R g) ∂cellMeasure G 4) := by ring
      _ = _ := by rw [hs]
  · simp only [h,ite_false,mul_zero]

/-- The full finite matrix trace of genuine unnormalized COM columns.
All off-relative-label entries remain until their COM levels are compared. -/
theorem finite_unnormalized_COM_matrix_trace {ι κ : Type*}
    (G : Geometry) (theta : Twist) (s : Finset ι) (t : Finset κ)
    (p : ι → Core ℕ ℂ) (r : κ → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 4) (hr : ∀ j, (r j).IsHomogeneous 4)
    (hpL : ∀ i, canonicalCOMLowerNat (p i)=0)
    (hrL : ∀ j, canonicalCOMLowerNat (r j)=0)
    (n : ι → ℕ) (m : κ → ℕ) (C : ι → κ → ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i ∈ s, ∑ j ∈ t, C i j * ip
      (natFourAnnihilator G theta R
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n i] (p i)) f)
      (natFourAnnihilator G theta R
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m j] (r j)) g)
        ∂cellMeasure G 2) =
    (2/4:ℂ) * ∑ i ∈ s, ∑ j ∈ t, if n i=m j then
      (4^(n i)*((n i).factorial:ℂ))*C i j *
        (∫ R, ip (natFourRemoval G theta (p i) (hp i) 0 R f)
          (natFourRemoval G theta (r j) (hr j) 0 R g) ∂cellMeasure G 4)
      else 0 := by
  have hi (i : ι) (j : κ) :=
    (natFourAnnihilator_descendant_cross_integrable G theta (p i) (r j)
      (hp i) (hr j) (n i) (m j) f g).const_mul (C i j)
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum t (fun j _ => hi i j))]
  simp_rw [integral_finsetSum t (fun j _ => hi _ j),integral_const_mul,
    natFourAnnihilator_descendant_integral G theta _ _ (hp _) (hr _) (hpL _) (hrL _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  apply Finset.sum_congr rfl
  intro j hjt
  split_ifs <;> ring


#print axioms natFourAnnihilator_descendant
#print axioms natFourAnnihilator_descendant_cross_integrable
#print axioms natFourAnnihilator_descendant_integral
#print axioms finite_unnormalized_COM_matrix_trace

end TorusLean.Shared.BosonNatFourUnnormalizedTrace
