import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (40812527564943992550 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((153286693339578358725 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((276424943798263615430625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((179011735113828222750375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2855709874385458727175 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((184019065795317321644625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-4633372289944850638725 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R11S11 :
    OAI.Laughlin.Certificate.errorRational 13 (5 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (5 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R11S11Row0,
    originalYRowSplitD13R11S11Row1,
    originalYRowSplitD13R11S11Row2,
    originalYRowSplitD13R11S11Row3,
    originalYRowSplitD13R11S11Row4,
    originalYRowSplitD13R11S11Row5,
    originalYRowSplitD13R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
