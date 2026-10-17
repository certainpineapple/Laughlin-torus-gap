import torus.shared.CellTiling
import torus.shared.MagneticCellUnfolding

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.CellTranslation
open MeasureTheory

/-- An arbitrary translated fundamental cell has exactly the same integral
for a genuinely lattice-periodic function. The period condition is pointwise. -/
theorem periodic_cellIntegral_translate_volume (G : Geometry)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E)
    (hF : ∀ p : ℤ × ℤ, ∀ z : ℂ,
      F (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) = F z)
    (x : ℂ) :
    (∫ z in cell G, F (z+x) ∂volume) = ∫ z in cell G, F z ∂volume := by
  letI := cellLatticeAction G
  letI : MeasurableConstVAdd (ℤ × ℤ) ℂ :=
    ⟨fun p => (continuous_const.add continuous_id).measurable⟩
  letI : VAddInvariantMeasure (ℤ × ℤ) ℂ (volume : Measure ℂ) :=
    ⟨fun p s _ => measure_preimage_add volume
      (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) s⟩
  have hf := cell_isAddFundamentalDomain_volume G
  have hp : Measure.QuasiMeasurePreserving (Equiv.addRight x).symm
      (volume : Measure ℂ) volume := by
    simpa only [Equiv.addRight_symm, Equiv.coe_addRight] using
      (measurePreserving_add_right (volume : Measure ℂ) (-x)).quasiMeasurePreserving
  have ht := hf.image_of_equiv (Equiv.addRight x) hp (Equiv.refl (ℤ × ℤ)) (by
    intro p z
    change (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) + x =
      TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + (z+x)
    exact add_assoc _ _ _)
  have he := hf.setIntegral_eq ht hF
  have hi := (measurePreserving_add_right (volume : Measure ℂ) x).setIntegral_image_emb
    (MeasurableEquiv.addRight x).measurableEmbedding F (cell G)
  exact hi.symm.trans he.symm

theorem periodic_cellIntegral_translate (G : Geometry) (k : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E)
    (hF : ∀ p : ℤ × ℤ, ∀ z : ℂ,
      F (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) = F z)
    (x : ℂ) :
    (∫ z, F (z+x) ∂cellMeasure G k) = ∫ z, F z ∂cellMeasure G k := by
  simp only [cellMeasure, integral_smul_measure]
  rw [periodic_cellIntegral_translate_volume G F hF x]

#print axioms periodic_cellIntegral_translate_volume
#print axioms periodic_cellIntegral_translate
end TorusLean.Shared.CellTranslation
