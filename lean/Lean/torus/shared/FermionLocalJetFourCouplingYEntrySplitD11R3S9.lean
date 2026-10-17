import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((8502774459177579525 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((212304908224516890915 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((484697220805009986007275 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((43997156302445938986345 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-16324214405706895758975 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((869846339334152704329855 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 11 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((129705452981181636615 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R3S9 :
    OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (1 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R3S9Row0,
    originalYRowSplitD11R3S9Row1,
    originalYRowSplitD11R3S9Row2,
    originalYRowSplitD11R3S9Row3,
    originalYRowSplitD11R3S9Row4,
    originalYRowSplitD11R3S9Row5,
    originalYRowSplitD11R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
