import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-819496972897685775 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-8195207388334982235 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((21896254401729824796075 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-56801294515779095811375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3413422916864588100825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((62769439796774187131325 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((6978497651169642675 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R9S11 :
    OAI.Laughlin.Certificate.errorRational 12 (4 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (4 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R9S11Row0,
    originalYRowSplitD12R9S11Row1,
    originalYRowSplitD12R9S11Row2,
    originalYRowSplitD12R9S11Row3,
    originalYRowSplitD12R9S11Row4,
    originalYRowSplitD12R9S11Row5,
    originalYRowSplitD12R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
