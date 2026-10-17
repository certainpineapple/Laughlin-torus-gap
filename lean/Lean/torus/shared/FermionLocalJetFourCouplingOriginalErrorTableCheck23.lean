import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Original degree-23 table identity isolated from the separate source identity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

/- Each exact original row is retained. For the first six rows every
ordered pair has total degree below 23. In the seventh row only the ordered
pair (9,9) can contribute; its exact V coefficient vanishes at every odd label. -/
open OAI.Laughlin.Certificate

private theorem degree23OddCenterV (i : Fin 12) :
    V (2*i.val+1) 23 23 7 8 8 = 0 := by
  fin_cases i <;> decide +kernel

private theorem degree23OriginalRowZero0 (r s : ℕ) :
    yRow 23 r s (rows[0]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero1 (r s : ℕ) :
    yRow 23 r s (rows[1]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero2 (r s : ℕ) :
    yRow 23 r s (rows[2]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero3 (r s : ℕ) :
    yRow 23 r s (rows[3]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero4 (r s : ℕ) :
    yRow 23 r s (rows[4]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero5 (r s : ℕ) :
    yRow 23 r s (rows[5]!) = 0 := by
  norm_num [rows,yRow,yEntry]

private theorem degree23OriginalRowZero6 (r s : ℕ)
    (hv : V r 23 23 7 8 8 = 0) :
    yRow 23 r s (rows[6]!) = 0 := by
  norm_num [rows,yRow,yEntry,hv]

theorem originalErrorTableCheck23 :
    OAI.Laughlin.Certificate.errorRational 23 = TorusLean.FermionM3.errorTable23 := by
  have htable : TorusLean.FermionM3.errorTable23 =
      (0 : Matrix (Fin 12) (Fin 12) ℚ) := by decide +kernel
  rw [htable]
  ext i j
  change Y 23 (2*i.val+1) (2*j.val+1) = 0
  rw [Y_expand,degree23OriginalRowZero0,degree23OriginalRowZero1,
    degree23OriginalRowZero2,degree23OriginalRowZero3,degree23OriginalRowZero4,
    degree23OriginalRowZero5,
    degree23OriginalRowZero6 _ _ (degree23OddCenterV i)]
  norm_num

#print axioms originalErrorTableCheck23
end TorusLean.Shared.FermionLocalJet.FourCoupling
