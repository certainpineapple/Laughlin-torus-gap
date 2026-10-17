import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-6941813770460836575 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-428807459542699568925 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1287236051131534268527125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((45886410457456998654225 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-297803095076657825325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((2674595621110306184775 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-867894319755606891825 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R9S11 :
    OAI.Laughlin.Certificate.errorRational 11 (4 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (4 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R9S11Row0,
    originalYRowSplitD11R9S11Row1,
    originalYRowSplitD11R9S11Row2,
    originalYRowSplitD11R9S11Row3,
    originalYRowSplitD11R9S11Row4,
    originalYRowSplitD11R9S11Row5,
    originalYRowSplitD11R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
