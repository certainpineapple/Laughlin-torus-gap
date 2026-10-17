import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((22663152100026511605 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((150841358828987800275 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((131135074003179026408475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((19832409641175641306055 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((12640993412636882725965 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((238848957077995594676205 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 11 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2492153607133646783775 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R9S9 :
    OAI.Laughlin.Certificate.errorRational 11 (4 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (4 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R9S9Row0,
    originalYRowSplitD11R9S9Row1,
    originalYRowSplitD11R9S9Row2,
    originalYRowSplitD11R9S9Row3,
    originalYRowSplitD11R9S9Row4,
    originalYRowSplitD11R9S9Row5,
    originalYRowSplitD11R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
