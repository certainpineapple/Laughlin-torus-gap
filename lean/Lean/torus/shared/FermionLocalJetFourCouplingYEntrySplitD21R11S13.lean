import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((204456789426574477918125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = (-3899618171547035857920000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 21 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = (1093313164148753280232500 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R11S13 :
    OAI.Laughlin.Certificate.errorRational 21 (5 : Fin 11) (6 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (5 : Fin 11) (6 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R11S13Row0,
    originalYRowSplitD21R11S13Row1,
    originalYRowSplitD21R11S13Row2,
    originalYRowSplitD21R11S13Row3,
    originalYRowSplitD21R11S13Row4,
    originalYRowSplitD21R11S13Row5,
    originalYRowSplitD21R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
