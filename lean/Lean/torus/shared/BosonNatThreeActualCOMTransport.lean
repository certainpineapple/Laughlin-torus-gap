import torus.shared.BosonNatThreeCOMColumnTransport
import torus.shared.BosonFiniteCertificateNatCOMBasisRank300
import torus.shared.BosonFiniteCertificateNatCOMBasisRank301
import torus.shared.BosonFiniteCertificateNatCOMBasisRank302
import torus.shared.BosonFiniteCertificateNatCOMBasisRank303
import torus.shared.BosonFiniteCertificateNatCOMBasisRank304
import torus.shared.BosonFiniteCertificateNatCOMBasisRank305
import torus.shared.BosonFiniteCertificateNatCOMBasisRank306
import torus.shared.BosonFiniteCertificateNatCOMBasisRank307
import torus.shared.BosonFiniteCertificateNatCOMBasisRank308

/-! The actual nine full COM families, the original source M3 matrices and
both genuine inverse-Gram factors, evaluated on actual physical annihilators.
No cross-relative-degree entry is discarded in these pointwise identities. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeActualCOMTransport
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeCOMColumnTransport
open scoped BigOperators ComplexConjugate

theorem k300_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k300COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k300COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k300COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p300Ginv * k300actualM3 * complexify p300Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k300occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k300occ j) g) := by
  have hST : complexify k300COMBasis * complexify k300COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k300_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k300COMRankCoefficient,inverseGramCoefficient,
    k300COMGramInverse,k300COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k300occ (complexify k300COMBasis)
      (complexify k300COMBasisInverse) (complexify p300Ginv) k300actualM3 hST
      k300COMDescendantFamily k300_COMDescendantFamily_column f g

theorem k301_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k301COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k301COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k301COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p301Ginv * k301actualM3 * complexify p301Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k301occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k301occ j) g) := by
  have hST : complexify k301COMBasis * complexify k301COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k301_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k301COMRankCoefficient,inverseGramCoefficient,
    k301COMGramInverse,k301COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k301occ (complexify k301COMBasis)
      (complexify k301COMBasisInverse) (complexify p301Ginv) k301actualM3 hST
      k301COMDescendantFamily k301_COMDescendantFamily_column f g

theorem k302_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k302COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k302COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k302COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p302Ginv * k302actualM3 * complexify p302Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k302occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k302occ j) g) := by
  have hST : complexify k302COMBasis * complexify k302COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k302_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k302COMRankCoefficient,inverseGramCoefficient,
    k302COMGramInverse,k302COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k302occ (complexify k302COMBasis)
      (complexify k302COMBasisInverse) (complexify p302Ginv) k302actualM3 hST
      k302COMDescendantFamily k302_COMDescendantFamily_column f g

theorem k303_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k303COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k303COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k303COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p303Ginv * k303actualM3 * complexify p303Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k303occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k303occ j) g) := by
  have hST : complexify k303COMBasis * complexify k303COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k303_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k303COMRankCoefficient,inverseGramCoefficient,
    k303COMGramInverse,k303COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k303occ (complexify k303COMBasis)
      (complexify k303COMBasisInverse) (complexify p303Ginv) k303actualM3 hST
      k303COMDescendantFamily k303_COMDescendantFamily_column f g

theorem k304_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k304COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k304COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k304COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p304Ginv * k304actualM3 * complexify p304Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k304occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k304occ j) g) := by
  have hST : complexify k304COMBasis * complexify k304COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k304_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k304COMRankCoefficient,inverseGramCoefficient,
    k304COMGramInverse,k304COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k304occ (complexify k304COMBasis)
      (complexify k304COMBasisInverse) (complexify p304Ginv) k304actualM3 hST
      k304COMDescendantFamily k304_COMDescendantFamily_column f g

theorem k305_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k305COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k305COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k305COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p305Ginv * k305actualM3 * complexify p305Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k305occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k305occ j) g) := by
  have hST : complexify k305COMBasis * complexify k305COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k305_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k305COMRankCoefficient,inverseGramCoefficient,
    k305COMGramInverse,k305COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k305occ (complexify k305COMBasis)
      (complexify k305COMBasisInverse) (complexify p305Ginv) k305actualM3 hST
      k305COMDescendantFamily k305_COMDescendantFamily_column f g

theorem k306_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k306COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k306COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k306COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p306Ginv * k306actualM3 * complexify p306Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k306occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k306occ j) g) := by
  have hST : complexify k306COMBasis * complexify k306COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k306_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k306COMRankCoefficient,inverseGramCoefficient,
    k306COMGramInverse,k306COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k306occ (complexify k306COMBasis)
      (complexify k306COMBasisInverse) (complexify p306Ginv) k306actualM3 hST
      k306COMDescendantFamily k306_COMDescendantFamily_column f g

theorem k307_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k307COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k307COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k307COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p307Ginv * k307actualM3 * complexify p307Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k307occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k307occ j) g) := by
  have hST : complexify k307COMBasis * complexify k307COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k307_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k307COMRankCoefficient,inverseGramCoefficient,
    k307COMGramInverse,k307COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k307occ (complexify k307COMBasis)
      (complexify k307COMBasisInverse) (complexify p307Ginv) k307actualM3 hST
      k307COMDescendantFamily k307_COMDescendantFamily_column f g

theorem k308_actual_COM_inverseGram_rows (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, k308COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k308COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k308COMDescendantFamily j) g)) =
    ∑ i, ∑ j, (complexify p308Ginv * k308actualM3 * complexify p308Ginv) i j *
      ip (natThreeAnnihilator G theta R (natOccupationColumns k308occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns k308occ j) g) := by
  have hST : complexify k308COMBasis * complexify k308COMBasisInverse = 1 := by
    rw [←complexify_mul_rect,k308_COMBasis_inverse_left,complexify_one_rat]
  simpa only [k308COMRankCoefficient,inverseGramCoefficient,
    k308COMGramInverse,k308COMSourceForm] using
    actual_COM_inverseGram_rows G theta R k308occ (complexify k308COMBasis)
      (complexify k308COMBasisInverse) (complexify p308Ginv) k308actualM3 hST
      k308COMDescendantFamily k308_COMDescendantFamily_column f g

end TorusLean.Shared.BosonNatThreeActualCOMTransport
