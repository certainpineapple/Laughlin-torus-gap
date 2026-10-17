import torus.shared.BosonNatThreeActualCOMTransport
import torus.shared.BosonNatThreeCellLift

/-! The original full L3 of each actual source rank density at charge two,
expressed in its complete true COM family. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeActualCOMCellLift
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonNatThreeCOMColumnTransport
open TorusLean.Shared.BosonNatThreeRankCongruence
open TorusLean.Shared.BosonNatThreeMatrixLiftCongruence
open TorusLean.Shared.BosonNatThreeCellLift
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

theorem actual_COM_family_particle {r : ℕ} (occ : Fin r → (Fin 9 →₀ ℕ))
    (hN : ∀ i, (occ i).degree=3) (S : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j))) (i : Fin r) :
    (w i).IsHomogeneous 3 := by
  rw [actual_COM_columns_eq_seedCombination occ S w hw]
  exact seedCombination_particle _ (natOccupationColumns_particle occ hN) S i

theorem actual_COM_cell_lift {r : ℕ} (G : Geometry) (theta : Twist) (k : ℕ)
    (occ : Fin r → (Fin 9 →₀ ℕ)) (hN : ∀ i, (occ i).degree=3)
    (S T J M : Matrix (Fin r) (Fin r) ℂ) (hST : S*T=1)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j)))
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k w (actual_COM_family_particle occ hN S w hw)
      ((T*J*Tᴴ)*(Sᴴ*M*S)*(T*J*Tᴴ)) f =
    natMatrixCellLiftForm G theta k (natOccupationColumns occ)
      (natOccupationColumns_particle occ hN) (J*M*J) f := by
  rw [natMatrixCellLiftForm_eq_annihilator,natMatrixCellLiftForm_eq_annihilator]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  exact congrArg Complex.re (actual_COM_inverseGram_rows G theta R occ S T J M hST w hw f f)

theorem k300_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k300COMDescendantFamily
      (actual_COM_family_particle k300occ k300_particle_degree (complexify k300COMBasis)
        k300COMDescendantFamily k300_COMDescendantFamily_column)
      k300COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k300occ)
      (natOccupationColumns_particle k300occ k300_particle_degree)
      (complexify p300Ginv * k300actualM3 * complexify p300Ginv) f := by
  have hST : complexify k300COMBasis * complexify k300COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k300_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k300COMRankCoefficient,inverseGramCoefficient,
    k300COMGramInverse,k300COMSourceForm] using
    actual_COM_cell_lift G theta 2 k300occ k300_particle_degree
      (complexify k300COMBasis) (complexify k300COMBasisInverse)
      (complexify p300Ginv) k300actualM3 hST
      k300COMDescendantFamily k300_COMDescendantFamily_column f

theorem k301_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k301COMDescendantFamily
      (actual_COM_family_particle k301occ k301_particle_degree (complexify k301COMBasis)
        k301COMDescendantFamily k301_COMDescendantFamily_column)
      k301COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k301occ)
      (natOccupationColumns_particle k301occ k301_particle_degree)
      (complexify p301Ginv * k301actualM3 * complexify p301Ginv) f := by
  have hST : complexify k301COMBasis * complexify k301COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k301_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k301COMRankCoefficient,inverseGramCoefficient,
    k301COMGramInverse,k301COMSourceForm] using
    actual_COM_cell_lift G theta 2 k301occ k301_particle_degree
      (complexify k301COMBasis) (complexify k301COMBasisInverse)
      (complexify p301Ginv) k301actualM3 hST
      k301COMDescendantFamily k301_COMDescendantFamily_column f

theorem k302_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k302COMDescendantFamily
      (actual_COM_family_particle k302occ k302_particle_degree (complexify k302COMBasis)
        k302COMDescendantFamily k302_COMDescendantFamily_column)
      k302COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k302occ)
      (natOccupationColumns_particle k302occ k302_particle_degree)
      (complexify p302Ginv * k302actualM3 * complexify p302Ginv) f := by
  have hST : complexify k302COMBasis * complexify k302COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k302_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k302COMRankCoefficient,inverseGramCoefficient,
    k302COMGramInverse,k302COMSourceForm] using
    actual_COM_cell_lift G theta 2 k302occ k302_particle_degree
      (complexify k302COMBasis) (complexify k302COMBasisInverse)
      (complexify p302Ginv) k302actualM3 hST
      k302COMDescendantFamily k302_COMDescendantFamily_column f

theorem k303_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k303COMDescendantFamily
      (actual_COM_family_particle k303occ k303_particle_degree (complexify k303COMBasis)
        k303COMDescendantFamily k303_COMDescendantFamily_column)
      k303COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k303occ)
      (natOccupationColumns_particle k303occ k303_particle_degree)
      (complexify p303Ginv * k303actualM3 * complexify p303Ginv) f := by
  have hST : complexify k303COMBasis * complexify k303COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k303_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k303COMRankCoefficient,inverseGramCoefficient,
    k303COMGramInverse,k303COMSourceForm] using
    actual_COM_cell_lift G theta 2 k303occ k303_particle_degree
      (complexify k303COMBasis) (complexify k303COMBasisInverse)
      (complexify p303Ginv) k303actualM3 hST
      k303COMDescendantFamily k303_COMDescendantFamily_column f

theorem k304_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k304COMDescendantFamily
      (actual_COM_family_particle k304occ k304_particle_degree (complexify k304COMBasis)
        k304COMDescendantFamily k304_COMDescendantFamily_column)
      k304COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k304occ)
      (natOccupationColumns_particle k304occ k304_particle_degree)
      (complexify p304Ginv * k304actualM3 * complexify p304Ginv) f := by
  have hST : complexify k304COMBasis * complexify k304COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k304_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k304COMRankCoefficient,inverseGramCoefficient,
    k304COMGramInverse,k304COMSourceForm] using
    actual_COM_cell_lift G theta 2 k304occ k304_particle_degree
      (complexify k304COMBasis) (complexify k304COMBasisInverse)
      (complexify p304Ginv) k304actualM3 hST
      k304COMDescendantFamily k304_COMDescendantFamily_column f

theorem k305_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k305COMDescendantFamily
      (actual_COM_family_particle k305occ k305_particle_degree (complexify k305COMBasis)
        k305COMDescendantFamily k305_COMDescendantFamily_column)
      k305COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k305occ)
      (natOccupationColumns_particle k305occ k305_particle_degree)
      (complexify p305Ginv * k305actualM3 * complexify p305Ginv) f := by
  have hST : complexify k305COMBasis * complexify k305COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k305_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k305COMRankCoefficient,inverseGramCoefficient,
    k305COMGramInverse,k305COMSourceForm] using
    actual_COM_cell_lift G theta 2 k305occ k305_particle_degree
      (complexify k305COMBasis) (complexify k305COMBasisInverse)
      (complexify p305Ginv) k305actualM3 hST
      k305COMDescendantFamily k305_COMDescendantFamily_column f

theorem k306_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k306COMDescendantFamily
      (actual_COM_family_particle k306occ k306_particle_degree (complexify k306COMBasis)
        k306COMDescendantFamily k306_COMDescendantFamily_column)
      k306COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k306occ)
      (natOccupationColumns_particle k306occ k306_particle_degree)
      (complexify p306Ginv * k306actualM3 * complexify p306Ginv) f := by
  have hST : complexify k306COMBasis * complexify k306COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k306_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k306COMRankCoefficient,inverseGramCoefficient,
    k306COMGramInverse,k306COMSourceForm] using
    actual_COM_cell_lift G theta 2 k306occ k306_particle_degree
      (complexify k306COMBasis) (complexify k306COMBasisInverse)
      (complexify p306Ginv) k306actualM3 hST
      k306COMDescendantFamily k306_COMDescendantFamily_column f

theorem k307_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k307COMDescendantFamily
      (actual_COM_family_particle k307occ k307_particle_degree (complexify k307COMBasis)
        k307COMDescendantFamily k307_COMDescendantFamily_column)
      k307COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k307occ)
      (natOccupationColumns_particle k307occ k307_particle_degree)
      (complexify p307Ginv * k307actualM3 * complexify p307Ginv) f := by
  have hST : complexify k307COMBasis * complexify k307COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k307_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k307COMRankCoefficient,inverseGramCoefficient,
    k307COMGramInverse,k307COMSourceForm] using
    actual_COM_cell_lift G theta 2 k307occ k307_particle_degree
      (complexify k307COMBasis) (complexify k307COMBasisInverse)
      (complexify p307Ginv) k307actualM3 hST
      k307COMDescendantFamily k307_COMDescendantFamily_column f

theorem k308_actual_source_L3_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 k308COMDescendantFamily
      (actual_COM_family_particle k308occ k308_particle_degree (complexify k308COMBasis)
        k308COMDescendantFamily k308_COMDescendantFamily_column)
      k308COMRankCoefficient f =
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k308occ)
      (natOccupationColumns_particle k308occ k308_particle_degree)
      (complexify p308Ginv * k308actualM3 * complexify p308Ginv) f := by
  have hST : complexify k308COMBasis * complexify k308COMBasisInverse=1 := by
    rw [←complexify_mul_rect,k308_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k308COMRankCoefficient,inverseGramCoefficient,
    k308COMGramInverse,k308COMSourceForm] using
    actual_COM_cell_lift G theta 2 k308occ k308_particle_degree
      (complexify k308COMBasis) (complexify k308COMBasisInverse)
      (complexify p308Ginv) k308actualM3 hST
      k308COMDescendantFamily k308_COMDescendantFamily_column f

end TorusLean.Shared.BosonNatThreeActualCOMCellLift
