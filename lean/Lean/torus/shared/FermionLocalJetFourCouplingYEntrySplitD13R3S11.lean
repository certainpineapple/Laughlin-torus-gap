import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((319280122428000547275 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-426205811584079606475 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((432610736576007190853025 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-474022567920351013311825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-11400814581342552736425 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-677160481944788969423175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-18825999575116201100325 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S11 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S11Row0,
    originalYRowSplitD13R3S11Row1,
    originalYRowSplitD13R3S11Row2,
    originalYRowSplitD13R3S11Row3,
    originalYRowSplitD13R3S11Row4,
    originalYRowSplitD13R3S11Row5,
    originalYRowSplitD13R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
