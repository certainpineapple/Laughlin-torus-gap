import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD2R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((353813604943693953 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((193001494390477023921 / 18790481920) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-10768213063700762737619 / 15032385536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((4563712153716963974355 / 7516192768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((22095609786793160384465 / 45097156608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5048694375416061913141 / 60129542144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD2R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 2 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-63830619095902031895 / 536870912) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD2R1S1 :
    OAI.Laughlin.Certificate.errorRational 2 (0 : Fin 1) (0 : Fin 1) =
      TorusLean.FermionM3.errorTable02 (0 : Fin 1) (0 : Fin 1) := by
  change OAI.Laughlin.Certificate.Y 2 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD2R1S1Row0,
    originalYRowSplitD2R1S1Row1,
    originalYRowSplitD2R1S1Row2,
    originalYRowSplitD2R1S1Row3,
    originalYRowSplitD2R1S1Row4,
    originalYRowSplitD2R1S1Row5,
    originalYRowSplitD2R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable02]

#print axioms originalYEntrySplitD2R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
