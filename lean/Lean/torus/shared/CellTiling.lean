import torus.shared.CellMeasure
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Exact integer tiling and integral unfolding of the actual half-open cell

The cell and lattice basis are exactly those already used by the physical
cell inner product. Integer floors of the actual inverse lattice coordinates
give an everywhere unique cell decomposition; no fundamental-domain input is
assumed. The final integral identity uses the original plane measure
`(1 / π) * Lebesgue`, whose restriction is the existing charge-one cell measure.
There is no additional area or flux normalization.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared

open Set MeasureTheory
open scoped ENNReal Topology Pointwise

/-- Actual inverse coordinates of the fixed physical lattice basis. -/
def cellCoordinates (G : Geometry) (z : ℂ) : ℂ := (cellCoordinateEquiv G).symm z

/-- Integer coordinate vector; the image is the original latticePeriod. -/
def cellIntegerCoordinates (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem cellCoordinateEquiv_integer (G : Geometry) (p : ℤ × ℤ) :
    cellCoordinateEquiv G (cellIntegerCoordinates p) =
      TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p := by
  simp [cellCoordinateEquiv_apply, cellIntegerCoordinates,
    TorusLean.Geometry.latticePeriod]

theorem cellCoordinates_period (G : Geometry) (p : ℤ × ℤ) :
    cellCoordinates G (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) =
      cellIntegerCoordinates p := by
  rw [← cellCoordinateEquiv_integer, cellCoordinates,
    LinearEquiv.symm_apply_apply]

theorem cellCoordinates_add_period (G : Geometry) (z : ℂ) (p : ℤ × ℤ) :
    cellCoordinates G (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) =
      cellCoordinates G z + cellIntegerCoordinates p := by
  change (cellCoordinateEquiv G).symm
      (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) = _
  rw [map_add]
  exact congrArg (fun w => cellCoordinates G z + w) (cellCoordinates_period G p)

theorem mem_cell_iff_coordinates (G : Geometry) (z : ℂ) :
    z ∈ cell G ↔ (cellCoordinates G z).re ∈ Ico (0 : ℝ) 1 ∧
      (cellCoordinates G z).im ∈ Ico (0 : ℝ) 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w.re ∈ Ico (0 : ℝ) 1 ∧ w.im ∈ Ico (0 : ℝ) 1 at hw
    simpa only [cellCoordinates, LinearEquiv.symm_apply_apply] using hw
  · intro hz
    exact ⟨(cellCoordinateEquiv G).symm z, hz,
      (cellCoordinateEquiv G).apply_symm_apply z⟩

/-- The actual tile index, obtained from the two real floors. -/
def cellTileIndex (G : Geometry) (z : ℂ) : ℤ × ℤ :=
  (⌊(cellCoordinates G z).re⌋, ⌊(cellCoordinates G z).im⌋)

/-- The actual representative in the canonical half-open cell. -/
def cellRemainder (G : Geometry) (z : ℂ) : ℂ :=
  cellCoordinateEquiv G
    (Complex.ofReal (Int.fract (cellCoordinates G z).re) +
      Complex.ofReal (Int.fract (cellCoordinates G z).im) * Complex.I)

theorem cellRemainder_mem (G : Geometry) (z : ℂ) : cellRemainder G z ∈ cell G := by
  rw [mem_cell_iff_coordinates]
  simp only [cellRemainder, cellCoordinates, LinearEquiv.symm_apply_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, zero_add, add_zero]
  exact ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩

theorem cell_decomposition (G : Geometry) (z : ℂ) :
    z = cellRemainder G z +
      TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (cellTileIndex G z) := by
  have hs : cellCoordinates G z =
      (Complex.ofReal (Int.fract (cellCoordinates G z).re) +
        Complex.ofReal (Int.fract (cellCoordinates G z).im) * Complex.I) +
      cellIntegerCoordinates (cellTileIndex G z) := by
    apply Complex.ext <;> simp [cellIntegerCoordinates, cellTileIndex,
      Int.fract_add_floor]
  calc
    z = cellCoordinateEquiv G (cellCoordinates G z) :=
      ((cellCoordinateEquiv G).apply_symm_apply z).symm
    _ = _ := by
      rw [hs, map_add, cellCoordinateEquiv_integer]
      rfl

/-- An actual cell representative determines its unique integer tile. -/
theorem cellTileIndex_eq_of_decomposition (G : Geometry) (z w : ℂ) (p : ℤ × ℤ)
    (hw : w ∈ cell G)
    (hz : z = w + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) :
    cellTileIndex G z = p := by
  have hc := (mem_cell_iff_coordinates G w).mp hw
  have hr : ⌊(cellCoordinates G w).re⌋ = 0 := Int.floor_eq_zero_iff.mpr hc.1
  have hi : ⌊(cellCoordinates G w).im⌋ = 0 := Int.floor_eq_zero_iff.mpr hc.2
  rw [hz]
  apply Prod.ext <;> simp [cellTileIndex, cellCoordinates_add_period,
    cellIntegerCoordinates, Int.floor_add_intCast, hr, hi]

/-- Translate of the actual cell, indexed by the original integer periods. -/
def cellTranslate (G : Geometry) (p : ℤ × ℤ) : Set ℂ :=
  (fun z => z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) '' cell G

theorem cellTranslate_pairwise_disjoint (G : Geometry) :
    Pairwise (fun p q : ℤ × ℤ => Disjoint (cellTranslate G p) (cellTranslate G q)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro z hzp hzq
  obtain ⟨w, hw, hwz⟩ := hzp
  obtain ⟨v, hv, hvz⟩ := hzq
  have hp := cellTileIndex_eq_of_decomposition G z w p hw hwz.symm
  have hq := cellTileIndex_eq_of_decomposition G z v q hv hvz.symm
  exact hpq (hp.symm.trans hq)

theorem cellTranslate_cover (G : Geometry) :
    (⋃ p : ℤ × ℤ, cellTranslate G p) = univ := by
  apply eq_univ_iff_forall.mpr
  intro z
  exact mem_iUnion.mpr ⟨cellTileIndex G z, cellRemainder G z,
    cellRemainder_mem G z, (cell_decomposition G z).symm⟩

theorem latticePeriod_neg (G : Geometry) (p : ℤ × ℤ) :
    TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (-p) =
      -TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p := by
  simp [TorusLean.Geometry.latticePeriod, neg_mul, add_comm]

theorem cell_existsUnique_shift (G : Geometry) (z : ℂ) :
    ∃! p : ℤ × ℤ,
      TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z ∈ cell G := by
  refine ⟨-cellTileIndex G z, ?_, ?_⟩
  · have hs : TorusLean.Geometry.latticePeriod G.omega1 G.omega2
        (-cellTileIndex G z) + z = cellRemainder G z := by
      rw [latticePeriod_neg]
      calc
        _ = -TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (cellTileIndex G z) +
            (cellRemainder G z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2
              (cellTileIndex G z)) :=
          congrArg (fun w : ℂ =>
            -TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (cellTileIndex G z) + w)
              (cell_decomposition G z)
        _ = _ := by simp [add_comm, add_left_comm, add_assoc]
    change TorusLean.Geometry.latticePeriod G.omega1 G.omega2
      (-cellTileIndex G z) + z ∈ cell G
    rw [hs]
    exact cellRemainder_mem G z
  · intro p hp
    have hz : z =
        (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) +
          TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (-p) := by
      rw [latticePeriod_neg]
      simp [add_comm, add_left_comm, add_assoc]
    have hi := cellTileIndex_eq_of_decomposition G z
      (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) (-p) hp hz
    simpa using (congrArg (fun q : ℤ × ℤ => -q) hi).symm

/-- The actual integer-lattice translation action, always tied to the fixed G.
It is installed locally, so distinct geometries never share a global action. -/
@[instance_reducible]
def cellLatticeAction (G : Geometry) : AddAction (ℤ × ℤ) ℂ where
  vadd p z := TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z
  zero_vadd z := by
    change TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (0 : ℤ × ℤ) + z = z
    simp [TorusLean.Geometry.latticePeriod]
  add_vadd p q z := by
    change TorusLean.Geometry.latticePeriod G.omega1 G.omega2 (p + q) + z =
      TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p +
        (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 q + z)
    rw [TorusLean.Geometry.latticePeriod_add]
    exact add_assoc _ _ _

/-- Fundamental-domain status is proved from everywhere unique actual floors. -/
theorem cell_isAddFundamentalDomain_volume (G : Geometry) :
    letI := cellLatticeAction G
    IsAddFundamentalDomain (ℤ × ℤ) (cell G) (volume : Measure ℂ) := by
  letI := cellLatticeAction G
  apply IsAddFundamentalDomain.mk' (measurableSet_cell G).nullMeasurableSet
  exact cell_existsUnique_shift G

private theorem cellLatticeMeasurable (G : Geometry) :
    letI := cellLatticeAction G
    MeasurableConstVAdd (ℤ × ℤ) ℂ := by
  letI := cellLatticeAction G
  refine ⟨?_⟩
  intro p
  exact (continuous_const.add continuous_id).measurable

private theorem cellLatticeVolumeInvariant (G : Geometry) :
    letI := cellLatticeAction G
    VAddInvariantMeasure (ℤ × ℤ) ℂ (volume : Measure ℂ) := by
  letI := cellLatticeAction G
  refine ⟨?_⟩
  intro p s _hs
  exact measure_preimage_add volume
    (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) s

/-- The unchanged plane normalization restricts to the charge-one cell measure. -/
theorem normalizedPlane_restrict_cell (G : Geometry) :
    (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (cell G) =
      cellMeasure G 1 := by
  rw [Measure.restrict_smul, cellMeasure]
  simp

theorem cell_isAddFundamentalDomain_normalizedPlane (G : Geometry) :
    letI := cellLatticeAction G
    IsAddFundamentalDomain (ℤ × ℤ) (cell G)
      (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := by
  letI := cellLatticeAction G
  apply IsAddFundamentalDomain.mk' (measurableSet_cell G).nullMeasurableSet
  exact cell_existsUnique_shift G

/-- Lebesgue integral unfolding through the actual disjoint integer cell tiling. -/
theorem tsum_cellIntegral_eq_planeIntegral_volume (G : Geometry)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (hf : Integrable f (volume : Measure ℂ)) :
    (∑' p : ℤ × ℤ, ∫ z in cell G,
      f (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p) ∂volume) =
      ∫ z, f z ∂volume := by
  letI := cellLatticeAction G
  letI := cellLatticeMeasurable G
  letI := cellLatticeVolumeInvariant G
  have hi := (cell_isAddFundamentalDomain_volume G).integral_eq_tsum'' f hf
  change (∫ z, f z ∂volume) = ∑' p : ℤ × ℤ,
    ∫ z in cell G, f (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z)
      ∂volume at hi
  simpa only [add_comm] using hi.symm

/-- Physical charge-one unfolding: μ₁ on the cell and 1/π Lebesgue on the
plane. In particular no extra π*M area normalization is present. -/
theorem tsum_cellIntegral_eq_planeIntegral (G : Geometry)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E)
    (hf : Integrable f (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ))) :
    (∑' p : ℤ × ℤ, ∫ z,
      f (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p)
        ∂cellMeasure G 1) =
      ∫ z, f z ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := by
  letI := cellLatticeAction G
  letI := cellLatticeMeasurable G
  letI := cellLatticeVolumeInvariant G
  letI : VAddInvariantMeasure (ℤ × ℤ) ℂ
      (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := inferInstance
  have hi := (cell_isAddFundamentalDomain_normalizedPlane G).integral_eq_tsum'' f hf
  change (∫ z, f z ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ))) =
    ∑' p : ℤ × ℤ, ∫ z,
      f (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z)
        ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (cell G) at hi
  rw [normalizedPlane_restrict_cell] at hi
  simpa only [add_comm] using hi.symm

/-- Tonelli form of the same physical unfolding, available before proving a
particular integrability or absolute summability estimate. -/
theorem tsum_cellLIntegral_eq_planeLIntegral (G : Geometry) (f : ℂ → ℝ≥0∞) :
    (∑' p : ℤ × ℤ, ∫⁻ z,
      f (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p)
        ∂cellMeasure G 1) =
      ∫⁻ z, f z ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := by
  letI := cellLatticeAction G
  letI := cellLatticeMeasurable G
  letI := cellLatticeVolumeInvariant G
  letI : VAddInvariantMeasure (ℤ × ℤ) ℂ
      (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := inferInstance
  have hi := (cell_isAddFundamentalDomain_normalizedPlane G).lintegral_eq_tsum'' f
  change (∫⁻ z, f z ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ))) =
    ∑' p : ℤ × ℤ, ∫⁻ z,
      f (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z)
        ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (cell G) at hi
  rw [normalizedPlane_restrict_cell] at hi
  simpa only [add_comm] using hi.symm

/-- Genuine summability of the cell integrals of the translated absolute
value, derived from plane integrability and the proved actual tiling. -/
theorem summable_cellIntegral_norm (G : Geometry)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E)
    (hf : Integrable f (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ))) :
    Summable (fun p : ℤ × ℤ => ∫ z,
      ‖f (z + TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p)‖
        ∂cellMeasure G 1) := by
  letI := cellLatticeAction G
  letI := cellLatticeMeasurable G
  letI := cellLatticeVolumeInvariant G
  letI : VAddInvariantMeasure (ℤ × ℤ) ℂ
      (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)) := inferInstance
  have hsum := (cell_isAddFundamentalDomain_normalizedPlane G).sum_restrict
  have hfSum : Integrable f (Measure.sum (fun p : ℤ × ℤ =>
      (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (p +ᵥ cell G))) := by
    rw [hsum]
    exact hf
  apply hfSum.summable_integral.congr
  intro p
  have hi := (measurePreserving_vadd p
    (ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ))).setIntegral_image_emb
      (measurableEmbedding_const_vadd p) (fun z => ‖f z‖) (cell G)
  change (∫ z, ‖f z‖
      ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (p +ᵥ cell G)) =
    ∫ z, ‖f (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z)‖
      ∂(ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ)).restrict (cell G) at hi
  rw [normalizedPlane_restrict_cell] at hi
  simpa only [add_comm] using hi

#print axioms cellCoordinateEquiv_integer
#print axioms cellCoordinates_period
#print axioms cellCoordinates_add_period
#print axioms mem_cell_iff_coordinates
#print axioms cellRemainder_mem
#print axioms cell_decomposition
#print axioms cellTileIndex_eq_of_decomposition
#print axioms cellTranslate_pairwise_disjoint
#print axioms cellTranslate_cover
#print axioms latticePeriod_neg
#print axioms cell_existsUnique_shift
#print axioms cell_isAddFundamentalDomain_volume
#print axioms normalizedPlane_restrict_cell
#print axioms cell_isAddFundamentalDomain_normalizedPlane
#print axioms tsum_cellIntegral_eq_planeIntegral_volume
#print axioms tsum_cellIntegral_eq_planeIntegral
#print axioms tsum_cellLIntegral_eq_planeLIntegral
#print axioms summable_cellIntegral_norm

end TorusLean.Shared
