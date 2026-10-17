import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Original degree-22 table identity isolated from the separate source identity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

/- Each exact original row is retained. For the first six rows every
ordered pair has total degree below 22. In the seventh row only the ordered
pair (9,9) can contribute; its exact V coefficient vanishes at every odd label. -/
open OAI.Laughlin.Certificate

private theorem degree22OddCenterV (i : Fin 11) :
    V (2*i.val+1) 22 23 7 8 8 = 0 := by
  fin_cases i <;> decide +kernel

private theorem degree22OriginalRowZero0 (r s : ℕ) :
    yRow 22 r s (rows[0]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero1 (r s : ℕ) :
    yRow 22 r s (rows[1]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero2 (r s : ℕ) :
    yRow 22 r s (rows[2]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero3 (r s : ℕ) :
    yRow 22 r s (rows[3]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero4 (r s : ℕ) :
    yRow 22 r s (rows[4]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero5 (r s : ℕ) :
    yRow 22 r s (rows[5]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree22OriginalRowZero6 (r s : ℕ)
    (hv : V r 22 23 7 8 8 = 0) :
    yRow 22 r s (rows[6]!) = 0 := by
  norm_num [rows,yRow,yEntry,hv]

theorem originalErrorTableCheck22 :
    OAI.Laughlin.Certificate.errorRational 22 = TorusLean.FermionM3.errorTable22 := by
  have htable : TorusLean.FermionM3.errorTable22 =
      (0 : Matrix (Fin 11) (Fin 11) ℚ) := by decide +kernel
  rw [htable]
  ext i j
  change Y 22 (2*i.val+1) (2*j.val+1) = 0
  rw [Y_expand,degree22OriginalRowZero0,degree22OriginalRowZero1,
    degree22OriginalRowZero2,degree22OriginalRowZero3,degree22OriginalRowZero4,
    degree22OriginalRowZero5,
    degree22OriginalRowZero6 _ _ (degree22OddCenterV i)]
  norm_num

#print axioms originalErrorTableCheck22
end TorusLean.Shared.FermionLocalJet.FourCoupling
