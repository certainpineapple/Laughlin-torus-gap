import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = (-4741488309272801625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((880091628698734551225 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-10234722947662105314975 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1451866037922837738896625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-904407400268287723431225 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((4473516255597575294939775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 16 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-52325561654773862737275 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R7S9 :
    OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (3 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R7S9Row0,
    originalYRowSplitD16R7S9Row1,
    originalYRowSplitD16R7S9Row2,
    originalYRowSplitD16R7S9Row3,
    originalYRowSplitD16R7S9Row4,
    originalYRowSplitD16R7S9Row5,
    originalYRowSplitD16R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
