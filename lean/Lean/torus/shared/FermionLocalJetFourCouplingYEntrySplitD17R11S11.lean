import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((209483077173988550625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((364899094142049501890625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((230302946616762164000625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((349234116254286948691875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((10822049176278573502718625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-119556706315039318103625 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R11S11 :
    OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (5 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R11S11Row0,
    originalYRowSplitD17R11S11Row1,
    originalYRowSplitD17R11S11Row2,
    originalYRowSplitD17R11S11Row3,
    originalYRowSplitD17R11S11Row4,
    originalYRowSplitD17R11S11Row5,
    originalYRowSplitD17R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
