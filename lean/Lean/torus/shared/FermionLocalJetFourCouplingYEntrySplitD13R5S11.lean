import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-96982835474533706775 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-13862422182491538975 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-143102788388397946857375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((182246618359069217778825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-15325999558710323642775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1636025076525501355084875 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((11645839608836545676025 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R5S11 :
    OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (2 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R5S11Row0,
    originalYRowSplitD13R5S11Row1,
    originalYRowSplitD13R5S11Row2,
    originalYRowSplitD13R5S11Row3,
    originalYRowSplitD13R5S11Row4,
    originalYRowSplitD13R5S11Row5,
    originalYRowSplitD13R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
