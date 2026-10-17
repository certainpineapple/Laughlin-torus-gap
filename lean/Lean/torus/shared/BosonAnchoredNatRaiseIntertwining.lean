import torus.shared.BosonAnchoredNatLinearActions
import torus.shared.BosonFiniteCertificateNatCOM

/-! True untruncated natural-label COM raising and the original parameter
operator on actual locally finite periodized polynomials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.BosonAnchoredNatActions TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Shared.ThermalCoherentSeedWord
open scoped BigOperators ContDiff

theorem nat_linear_product_rule {I : Type*} [DecidableEq I]
    (A : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (hmul : ∀ p q, A (p*q) = A p*q+p*A q)
    (s : Finset I) (f : I → Core ℕ ℂ) :
    A (∏ i ∈ s, f i) = ∑ i ∈ s, A (f i) * ∏ l ∈ s.erase i, f l := by
  have hOne : A 1 = 0 := by
    simpa only [mul_one, one_mul, add_eq_left] using (hmul 1 1).symm
  induction s using Finset.induction_on with
  | empty => simp [hOne]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, hmul, ih, Finset.sum_insert ha]
    simp only [Finset.erase_insert ha]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := by intro h; subst b; exact ha hb
    rw [Finset.erase_insert_of_ne (Ne.symm hba), Finset.prod_insert (by simp [ha])]
    ring

theorem canonicalNatWord_update (k : ℕ) (j : Fin k → ℕ) (i : Fin k) (n : ℕ) :
    canonicalWord k (Function.update j i n) =
      MvPolynomial.X n * ∏ l ∈ Finset.univ.erase i, MvPolynomial.X (j l) := by
  unfold canonicalWord
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

theorem canonicalCOMRaiseNat_word (k : ℕ) (j : Fin k → ℕ) :
    canonicalCOMRaiseNat (canonicalWord k j) =
      ∑ i, (Real.sqrt (j i+1 : ℝ) : ℂ) • canonicalWord k (Function.update j i (j i+1)) := by
  rw [canonicalWord, nat_linear_product_rule _ canonicalCOMRaiseNat_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [canonicalCOMRaiseNat_X, canonicalNatWord_update]
  exact smul_mul_assoc _ _ _

theorem canonicalCOMRaiseNat_finiteWord {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) :
    canonicalCOMRaiseNat (finiteNatWordSeed k s c j) = raiseFiniteNatWordSeed k s c j := by
  simp only [finiteNatWordSeed, raiseFiniteNatWordSeed, map_sum, map_smul,
    canonicalCOMRaiseNat_word]

def naturalWordSpan (k : ℕ) : Submodule ℂ (Core ℕ ℂ) :=
  Submodule.span ℂ (Set.range (canonicalWord k : (Fin k → ℕ) → Core ℕ ℂ))

theorem naturalWordSpan_finite (k : ℕ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) :
    ∃ c : (Fin k → ℕ) →₀ ℂ, finiteNatWordSeed k c.support c id = p := by
  classical
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  exact ⟨c, by simpa only [finiteNatWordSeed, Finsupp.sum, id_eq] using hc⟩

theorem seedDualNat_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) :
    ContDiff ℝ ∞ (seedDualMapNat G theta q p) := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc]
  exact seedDualMapNat_finiteWord_contDiff G theta k q c.support c id

theorem seedDualNat_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) :
    HasDualBoundary G theta k (seedDualMapNat G theta q p) := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc]
  exact seedDualMapNat_finiteWord_boundary G theta k q c.support c id

theorem seedDualNat_raise_intertwining (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) (R : ℂ) :
    (Real.sqrt (k : ℝ) : ℂ) * parameterRaise k (seedDualMapNat G theta q p) R =
      seedDualMapNat G theta q (canonicalCOMRaiseNat p) R := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc, canonicalCOMRaiseNat_finiteWord]
  exact seedDualMapNat_raise_finiteWord G theta k q c.support c id R

theorem canonicalCOMRaiseNat_preserves_wordSpan (k : ℕ) (p : Core ℕ ℂ)
    (hp : p ∈ naturalWordSpan k) : canonicalCOMRaiseNat p ∈ naturalWordSpan k := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc, canonicalCOMRaiseNat_finiteWord]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨_, rfl⟩

end TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
