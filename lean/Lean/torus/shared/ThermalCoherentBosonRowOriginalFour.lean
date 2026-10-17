import torus.shared.ThermalCoherentBosonRowFourSource
import torus.shared.ThermalCoherentBosonRowFourTransport
import torus.shared.ThermalCoherentBosonRowFourCanonicalSource
import Mathlib.Data.List.OfFn

/-! The genuine raw K4 CCR term transported to the independently defined
original normal-word tensor. Its factorial annihilator denominator and all
original ordered terms remain explicit. This does not replace the tensor by
a relative-sector certificate, or assert a certificate bound. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowOriginalFour
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowFourTransport
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators
local instance originalFour_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private abbrev SourceIndex := RowIndex × Fin 9 × Fin 9
private def sourceLeft (z : SourceIndex) : Core ℕ ℂ :=
  rowThreeAuxiliarySeed z.1 z.2.1 * MvPolynomial.X z.2.2.val
private def sourceRight (z : SourceIndex) : Core ℕ ℂ :=
  rowThreeAuxiliarySeed z.1 z.2.2 * MvPolynomial.X z.2.1.val

private theorem sourceLeft_particle (z : SourceIndex) : (sourceLeft z).IsHomogeneous 4 :=
  (rowThreeAuxiliarySeed_sector z.1 z.2.1).mul (MvPolynomial.isHomogeneous_X ℂ z.2.2.val)
private theorem sourceRight_particle (z : SourceIndex) : (sourceRight z).IsHomogeneous 4 :=
  (rowThreeAuxiliarySeed_sector z.1 z.2.2).mul (MvPolynomial.isHomogeneous_X ℂ z.2.1.val)

private theorem source_dyad_sum (B : Core ℕ ℂ → Core ℕ ℂ → ℂ) :
    (∑ z : SourceIndex, B (sourceLeft z) (sourceRight z)) =
      ∑ ρ : RowIndex, ∑ i : Fin 9, ∑ j : Fin 9,
        B (rowThreeAuxiliarySeed ρ i * MvPolynomial.X j.val)
          (rowThreeAuxiliarySeed ρ j * MvPolynomial.X i.val) := by
  simp only [SourceIndex,Fintype.sum_prod_type,sourceLeft,sourceRight]

private theorem list_index_sum {α : Type*} (L : List α) (B : α → ℂ) :
    (∑ i : Fin L.length, B (L.get i)) = (L.map B).sum := by
  rw [←List.sum_ofFn]
  congr 1
  simpa only [Function.comp_def] using
    (List.map_ofFn (f := L.get) (g := B)).symm.trans (congrArg (List.map B) (List.ofFn_get L))

private abbrev OriginalIndex := Fin natFourOriginalTerms.length
private def originalLeft (z : OriginalIndex) : Core ℕ ℂ :=
  scaledWord factorialRootNat (natFourOriginalTerms.get z).creators
private def originalRight (z : OriginalIndex) : Core ℕ ℂ :=
  scaledWord factorialRootNat (natFourOriginalTerms.get z).annihilators
private def originalCoefficient (z : OriginalIndex) : ℂ :=
  ((natFourOriginalTerms.get z).coefficient : ℂ) /
    (natFourOrbitalMetric (natFourOriginalTerms.get z).annihilators : ℂ)

private theorem originalLeft_particle (z : OriginalIndex) :
    (originalLeft z).IsHomogeneous 4 := by
  rw [originalLeft,scaledWordNat_monomial]
  exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat _).trans
    (natFourOriginalTerms_shape _ (List.get_mem _ z)).1)
private theorem originalRight_particle (z : OriginalIndex) :
    (originalRight z).IsHomogeneous 4 := by
  rw [originalRight,scaledWordNat_monomial]
  exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat _).trans
    (natFourOriginalTerms_shape _ (List.get_mem _ z)).2.1)

private theorem original_source_rank_identity (f g : Core ℕ ℂ)
    (_hf : f.IsHomogeneous 4) (hg : g.IsHomogeneous 4) :
    (∑ z : SourceIndex, (1:ℂ) * star (natOccupationInner (sourceLeft z) f) *
      natOccupationInner (sourceRight z) g) =
      ∑ z : OriginalIndex, originalCoefficient z * star (natOccupationInner (originalLeft z) f) *
        natOccupationInner (originalRight z) g := by
  simp only [one_mul]
  rw [source_dyad_sum (fun p q => star (natOccupationInner p f)*natOccupationInner q g),
    ←canonicalNatFourOriginalOperator_decoded_rank_source f g hg,
    canonicalNatFourOriginalOperator_rank_form f g hg]
  symm
  exact list_index_sum natFourOriginalTerms (fun term =>
    (term.coefficient:ℂ)/(natFourOrbitalMetric term.annihilators:ℂ) *
      star (natOccupationInner (scaledWord factorialRootNat term.creators) f) *
        natOccupationInner (scaledWord factorialRootNat term.annihilators) g)

/-- Actual annihilator image of the independent original normal-word tensor. -/
def originalM4TensorCross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  (natFourOriginalTerms.map fun term =>
    (term.coefficient:ℂ)/(natFourOrbitalMetric term.annihilators:ℂ) *
      ip (natFourAnnihilator G theta R (scaledWord factorialRootNat term.creators) f)
        (natFourAnnihilator G theta R (scaledWord factorialRootNat term.annihilators) g)).sum

/-- Full-core K4 identity obtained from the true canonical N4 action by finite
coefficient separation. Neither input is restricted to a particle sector. -/
theorem actualRows_four_original_cross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ ρ : RowIndex, actualRowFourCross G theta ρ R f g) = originalM4TensorCross G theta R f g := by
  have h := finite_source_form_actual_cross G theta sourceLeft sourceRight
    originalLeft originalRight (fun _ => (1:ℂ)) originalCoefficient
    sourceLeft_particle sourceRight_particle originalLeft_particle originalRight_particle
    original_source_rank_identity R f g
  simp only [one_mul] at h
  rw [source_dyad_sum (fun p q => ip (natFourAnnihilator G theta R p f)
    (natFourAnnihilator G theta R q g))] at h
  simp only [actualRowFourCross_eq_source]
  exact h.trans (list_index_sum natFourOriginalTerms (fun term =>
    (term.coefficient:ℂ)/(natFourOrbitalMetric term.annihilators:ℂ) *
      ip (natFourAnnihilator G theta R (scaledWord factorialRootNat term.creators) f)
        (natFourAnnihilator G theta R (scaledWord factorialRootNat term.annihilators) g)))

end TorusLean.Shared.ThermalCoherentBosonRowOriginalFour
