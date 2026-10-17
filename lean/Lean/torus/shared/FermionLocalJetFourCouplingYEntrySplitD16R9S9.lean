import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (802405256748420168900 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((1047612322519464714075 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((5511938489639563720725 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((1578106751439769213935825 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((484388357781697292893725 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1745386976764820954862675 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 16 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-26190273117558281846625 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R9S9 :
    OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (4 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R9S9Row0,
    originalYRowSplitD16R9S9Row1,
    originalYRowSplitD16R9S9Row2,
    originalYRowSplitD16R9S9Row3,
    originalYRowSplitD16R9S9Row4,
    originalYRowSplitD16R9S9Row5,
    originalYRowSplitD16R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
