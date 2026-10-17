import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private def evalU (c z T p : ℕ) : ℤ :=
  if z ≤ T ∧ p ≤ T then
    (((List.range (min p z + 1)).filter (fun h => p + z ≤ T + h)).map
      (fun h => (-1 : ℤ) ^ (z-h) * (Nat.fast_choose z h : ℤ) *
        (Nat.fast_choose (T-z) (p-h) : ℤ) * (c : ℤ) ^ (p-h))).sum
  else 0

private theorem U_eq_evalU (c z T p : ℕ) :
    OAI.Laughlin.Certificate.U c z T p = evalU c z T p := by
  simp only [OAI.Laughlin.Certificate.U, evalU, Nat.choose_eq_fast_choose]

private def evalV (r D T p j k : ℕ) : ℤ :=
  if r ≤ j+k then evalU 1 r (j+k) j * evalU 1 (D-r) (T-r) p else 0

private theorem V_eq_evalV (r D T p j k : ℕ) :
    OAI.Laughlin.Certificate.V r D T p j k = evalV r D T p j k := by
  simp only [OAI.Laughlin.Certificate.V, evalV, U_eq_evalU]

private def evalEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℚ :=
  let (p,j,a) := e
  let (q,l,b) := f
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  if D ≤ T then
    (a : ℚ) * (b : ℚ) * (evalV r D T p j k : ℚ) * (evalV s D T q l i : ℚ) *
    (2 : ℚ) ^ (1-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)) *
    ((i.factorial : ℚ) * (k.factorial : ℚ) * (t.factorial : ℚ) /
      ((T-D).factorial : ℚ))
  else 0

private theorem yEntry_eq_evalEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    OAI.Laughlin.Certificate.yEntry D r s t e f = evalEntry D r s t e f := by
  simp only [OAI.Laughlin.Certificate.yEntry, evalEntry, V_eq_evalV]

private def evalRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => evalEntry D r s row.1 e f)).sum)).sum

private theorem yRow_eq_evalRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    OAI.Laughlin.Certificate.yRow D r s row = evalRow D r s row := by
  simp only [OAI.Laughlin.Certificate.yRow, evalRow, yEntry_eq_evalEntry]

private theorem originalYRowSplitD13R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-31275476917409923350075 / 256) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((4906626720597253265625 / 524288) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((50259142244779345799705025 / 2097152) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-17009750619365021092914075 / 524288) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((16048178917940394955023525 / 1048576) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((25839766234896685116148125 / 1048576) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

private theorem originalYRowSplitD13R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((136917832790658859822575 / 262144) : ℚ) := by
  rw [yRow_eq_evalRow]
  decide +kernel

theorem originalYEntrySplitD13R1S3 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (1 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (1 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S3Row0,
    originalYRowSplitD13R1S3Row1,
    originalYRowSplitD13R1S3Row2,
    originalYRowSplitD13R1S3Row3,
    originalYRowSplitD13R1S3Row4,
    originalYRowSplitD13R1S3Row5,
    originalYRowSplitD13R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
