import torus.shared.BosonFiniteCertificateNatRelativeRankComparisonCore

/-! The original cutoff comparison on each complete low-degree Nat relative
carrier equals the explicit rank cross form with coefficient J E J. This is
an equality for all genuine N3 homogeneous lowering vacua, without a supplied
span or positivity premise. It does not identify an original operator with
an arbitrary zero extension outside that carrier. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open scoped BigOperators ComplexConjugate ComplexOrder
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

def k300natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k300family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k300natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k300J) k300rowCertifiedComparison

theorem k300_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k300natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) := by
  rw [k300natRelativeFamily, natFamilySynthesis_rename, k300_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k300_nat_comparison_coefficient_posSemidef :
    k300natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k300J) k300rowCertifiedComparison
    k300_inverse_hermitian k300_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k300_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 0)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 0)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k300natRelativeFamily k300natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k300_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k300_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k300natRelativeFamily x = f :=
    (k300_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k300natRelativeFamily y = g :=
    (k300_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k300natRelativeFamily = complexify k300F := by
    rw [k300natRelativeFamily, natFamilyGram_rename, k300_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 0 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 0 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 0 f g = star x ⬝ᵥ (k300rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k300_nat_comparison_form, k300_actual_comparison_form]
    _ = natFamilyRankForm k300natRelativeFamily k300natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k300natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k300natRelativeFamily
        (complexify k300F) (complexify k300J) k300rowCertifiedComparison hGram
        k300_inverse_complex_right k300_inverse_complex_left x y).symm

#print axioms k300_nat_family_synthesis
#print axioms k300_nat_comparison_coefficient_posSemidef
#print axioms k300_nat_cutoff_comparison_rank_form

def k301natRelativeFamily : Fin 0 → Core ℕ ℂ := natFamilyOfFin9 k301family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k301natComparisonCoefficient : Matrix (Fin 0) (Fin 0) ℂ :=
  inverseGramCoefficient (complexify k301J) k301rowCertifiedComparison

theorem k301_nat_family_synthesis (x : Fin 0 → ℂ) :
    natFamilySynthesis k301natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) := by
  rw [k301natRelativeFamily, natFamilySynthesis_rename, k301_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k301_nat_comparison_coefficient_posSemidef :
    k301natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k301J) k301rowCertifiedComparison
    k301_inverse_hermitian k301_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k301_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 1)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 1)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k301natRelativeFamily k301natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k301_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k301_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k301natRelativeFamily x = f :=
    (k301_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k301natRelativeFamily y = g :=
    (k301_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k301natRelativeFamily = complexify k301F := by
    rw [k301natRelativeFamily, natFamilyGram_rename, k301_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 1 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 1 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 1 f g = star x ⬝ᵥ (k301rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k301_nat_comparison_form, k301_actual_comparison_form]
    _ = natFamilyRankForm k301natRelativeFamily k301natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k301natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k301natRelativeFamily
        (complexify k301F) (complexify k301J) k301rowCertifiedComparison hGram
        k301_inverse_complex_right k301_inverse_complex_left x y).symm

#print axioms k301_nat_family_synthesis
#print axioms k301_nat_comparison_coefficient_posSemidef
#print axioms k301_nat_cutoff_comparison_rank_form

def k302natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k302family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k302natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k302J) k302rowCertifiedComparison

theorem k302_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k302natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) := by
  rw [k302natRelativeFamily, natFamilySynthesis_rename, k302_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k302_nat_comparison_coefficient_posSemidef :
    k302natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k302J) k302rowCertifiedComparison
    k302_inverse_hermitian k302_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k302_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 2)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 2)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k302natRelativeFamily k302natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k302_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k302_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k302natRelativeFamily x = f :=
    (k302_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k302natRelativeFamily y = g :=
    (k302_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k302natRelativeFamily = complexify k302F := by
    rw [k302natRelativeFamily, natFamilyGram_rename, k302_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 2 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 2 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 2 f g = star x ⬝ᵥ (k302rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k302_nat_comparison_form, k302_actual_comparison_form]
    _ = natFamilyRankForm k302natRelativeFamily k302natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k302natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k302natRelativeFamily
        (complexify k302F) (complexify k302J) k302rowCertifiedComparison hGram
        k302_inverse_complex_right k302_inverse_complex_left x y).symm

#print axioms k302_nat_family_synthesis
#print axioms k302_nat_comparison_coefficient_posSemidef
#print axioms k302_nat_cutoff_comparison_rank_form

def k303natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k303family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k303natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k303J) k303rowCertifiedComparison

theorem k303_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k303natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) := by
  rw [k303natRelativeFamily, natFamilySynthesis_rename, k303_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k303_nat_comparison_coefficient_posSemidef :
    k303natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k303J) k303rowCertifiedComparison
    k303_inverse_hermitian k303_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k303_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 3)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 3)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k303natRelativeFamily k303natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k303_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k303_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k303natRelativeFamily x = f :=
    (k303_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k303natRelativeFamily y = g :=
    (k303_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k303natRelativeFamily = complexify k303F := by
    rw [k303natRelativeFamily, natFamilyGram_rename, k303_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 3 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 3 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 3 f g = star x ⬝ᵥ (k303rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k303_nat_comparison_form, k303_actual_comparison_form]
    _ = natFamilyRankForm k303natRelativeFamily k303natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k303natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k303natRelativeFamily
        (complexify k303F) (complexify k303J) k303rowCertifiedComparison hGram
        k303_inverse_complex_right k303_inverse_complex_left x y).symm

#print axioms k303_nat_family_synthesis
#print axioms k303_nat_comparison_coefficient_posSemidef
#print axioms k303_nat_cutoff_comparison_rank_form

def k304natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k304family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k304natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k304J) k304rowCertifiedComparison

theorem k304_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k304natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) := by
  rw [k304natRelativeFamily, natFamilySynthesis_rename, k304_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k304_nat_comparison_coefficient_posSemidef :
    k304natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k304J) k304rowCertifiedComparison
    k304_inverse_hermitian k304_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k304_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 4)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 4)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k304natRelativeFamily k304natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k304_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k304_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k304natRelativeFamily x = f :=
    (k304_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k304natRelativeFamily y = g :=
    (k304_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k304natRelativeFamily = complexify k304F := by
    rw [k304natRelativeFamily, natFamilyGram_rename, k304_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 4 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 4 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 4 f g = star x ⬝ᵥ (k304rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k304_nat_comparison_form, k304_actual_comparison_form]
    _ = natFamilyRankForm k304natRelativeFamily k304natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k304natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k304natRelativeFamily
        (complexify k304F) (complexify k304J) k304rowCertifiedComparison hGram
        k304_inverse_complex_right k304_inverse_complex_left x y).symm

#print axioms k304_nat_family_synthesis
#print axioms k304_nat_comparison_coefficient_posSemidef
#print axioms k304_nat_cutoff_comparison_rank_form

def k305natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k305family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k305natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k305J) k305rowCertifiedComparison

theorem k305_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k305natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) := by
  rw [k305natRelativeFamily, natFamilySynthesis_rename, k305_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k305_nat_comparison_coefficient_posSemidef :
    k305natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k305J) k305rowCertifiedComparison
    k305_inverse_hermitian k305_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k305_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 5)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 5)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k305natRelativeFamily k305natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k305_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k305_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k305natRelativeFamily x = f :=
    (k305_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k305natRelativeFamily y = g :=
    (k305_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k305natRelativeFamily = complexify k305F := by
    rw [k305natRelativeFamily, natFamilyGram_rename, k305_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 5 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 5 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 5 f g = star x ⬝ᵥ (k305rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k305_nat_comparison_form, k305_actual_comparison_form]
    _ = natFamilyRankForm k305natRelativeFamily k305natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k305natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k305natRelativeFamily
        (complexify k305F) (complexify k305J) k305rowCertifiedComparison hGram
        k305_inverse_complex_right k305_inverse_complex_left x y).symm

#print axioms k305_nat_family_synthesis
#print axioms k305_nat_comparison_coefficient_posSemidef
#print axioms k305_nat_cutoff_comparison_rank_form

def k306natRelativeFamily : Fin 2 → Core ℕ ℂ := natFamilyOfFin9 k306family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k306natComparisonCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  inverseGramCoefficient (complexify k306J) k306rowCertifiedComparison

theorem k306_nat_family_synthesis (x : Fin 2 → ℂ) :
    natFamilySynthesis k306natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) := by
  rw [k306natRelativeFamily, natFamilySynthesis_rename, k306_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k306_nat_comparison_coefficient_posSemidef :
    k306natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k306J) k306rowCertifiedComparison
    k306_inverse_hermitian k306_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k306_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 6)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 6)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k306natRelativeFamily k306natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k306_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k306_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k306natRelativeFamily x = f :=
    (k306_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k306natRelativeFamily y = g :=
    (k306_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k306natRelativeFamily = complexify k306F := by
    rw [k306natRelativeFamily, natFamilyGram_rename, k306_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 6 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 6 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 6 f g = star x ⬝ᵥ (k306rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k306_nat_comparison_form, k306_actual_comparison_form]
    _ = natFamilyRankForm k306natRelativeFamily k306natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k306natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k306natRelativeFamily
        (complexify k306F) (complexify k306J) k306rowCertifiedComparison hGram
        k306_inverse_complex_right k306_inverse_complex_left x y).symm

#print axioms k306_nat_family_synthesis
#print axioms k306_nat_comparison_coefficient_posSemidef
#print axioms k306_nat_cutoff_comparison_rank_form

def k307natRelativeFamily : Fin 1 → Core ℕ ℂ := natFamilyOfFin9 k307family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k307natComparisonCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k307J) k307rowCertifiedComparison

theorem k307_nat_family_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k307natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) := by
  rw [k307natRelativeFamily, natFamilySynthesis_rename, k307_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k307_nat_comparison_coefficient_posSemidef :
    k307natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k307J) k307rowCertifiedComparison
    k307_inverse_hermitian k307_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k307_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 7)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 7)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k307natRelativeFamily k307natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k307_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k307_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k307natRelativeFamily x = f :=
    (k307_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k307natRelativeFamily y = g :=
    (k307_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k307natRelativeFamily = complexify k307F := by
    rw [k307natRelativeFamily, natFamilyGram_rename, k307_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 7 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 7 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 7 f g = star x ⬝ᵥ (k307rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k307_nat_comparison_form, k307_actual_comparison_form]
    _ = natFamilyRankForm k307natRelativeFamily k307natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k307natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k307natRelativeFamily
        (complexify k307F) (complexify k307J) k307rowCertifiedComparison hGram
        k307_inverse_complex_right k307_inverse_complex_left x y).symm

#print axioms k307_nat_family_synthesis
#print axioms k307_nat_comparison_coefficient_posSemidef
#print axioms k307_nat_cutoff_comparison_rank_form

def k308natRelativeFamily : Fin 2 → Core ℕ ℂ := natFamilyOfFin9 k308family

/-- The genuine rank coefficient, retaining both inverse-Gram factors. -/
def k308natComparisonCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  inverseGramCoefficient (complexify k308J) k308rowCertifiedComparison

theorem k308_nat_family_synthesis (x : Fin 2 → ℂ) :
    natFamilySynthesis k308natRelativeFamily x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)) := by
  rw [k308natRelativeFamily, natFamilySynthesis_rename, k308_family_complex,
    canonicalFamilySynthesis_eq_block]

theorem k308_nat_comparison_coefficient_posSemidef :
    k308natComparisonCoefficient.PosSemidef :=
  inverseGramCoefficient_posSemidef (complexify k308J) k308rowCertifiedComparison
    k308_inverse_hermitian k308_row_certified_positive

/-- Original infinite COM and the actual degree<=8 counterterm on the full
true relative carrier; E is converted to J E J before taking Nat overlaps. -/
theorem k308_nat_cutoff_comparison_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 8)
    (hLf : canonicalCOMLowerNat f = 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 8)
    (hLg : canonicalCOMLowerNat g = 0) :
    canonicalNatCutoffComparisonForm f g =
      natFamilyRankForm k308natRelativeFamily k308natComparisonCoefficient f g := by
  obtain ⟨x, hx⟩ := (k308_nat_homogeneous_relative_kernel f hNf hdf).mp hLf
  obtain ⟨y, hy⟩ := (k308_nat_homogeneous_relative_kernel g hNg hdg).mp hLg
  have hfx : natFamilySynthesis k308natRelativeFamily x = f :=
    (k308_nat_family_synthesis x).trans hx
  have hgy : natFamilySynthesis k308natRelativeFamily y = g :=
    (k308_nat_family_synthesis y).trans hy
  have hGram : natFamilyGram k308natRelativeFamily = complexify k308F := by
    rw [k308natRelativeFamily, natFamilyGram_rename, k308_canonical_gram]
  rw [canonicalNatCutoffComparisonForm_low_eq_original 8 f g hdg (by decide),
    canonicalNatInfiniteComparisonForm_eq_finite 8 f g hNf hdf hNg hdg]
  calc
    canonicalNatComparisonForm 8 f g = star x ⬝ᵥ (k308rowCertifiedComparison *ᵥ y) := by
      rw [← hx, ← hy, k308_nat_comparison_form, k308_actual_comparison_form]
    _ = natFamilyRankForm k308natRelativeFamily k308natComparisonCoefficient f g := by
      rw [← hfx, ← hgy, k308natComparisonCoefficient]
      exact (natFamilyRankForm_inverseGram k308natRelativeFamily
        (complexify k308F) (complexify k308J) k308rowCertifiedComparison hGram
        k308_inverse_complex_right k308_inverse_complex_left x y).symm

#print axioms k308_nat_family_synthesis
#print axioms k308_nat_comparison_coefficient_posSemidef
#print axioms k308_nat_cutoff_comparison_rank_form

end TorusLean.BosonFiniteCertificate
