import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1070886273790732703679375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-208590550590474822144375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((9157572240306462939841875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-156843859455976110429886875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-50871878795661685972835625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((4991183593041335513306608125 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((183635333514081940079964375 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S5 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S5Row0,
    originalYRowSplitD16R1S5Row1,
    originalYRowSplitD16R1S5Row2,
    originalYRowSplitD16R1S5Row3,
    originalYRowSplitD16R1S5Row4,
    originalYRowSplitD16R1S5Row5,
    originalYRowSplitD16R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
