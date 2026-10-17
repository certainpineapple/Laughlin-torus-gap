import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin15_exact :
    threeMarginQ 15 = (295245254154499:ℚ)/1180980000000000000 := by
  decide +kernel

theorem margin15_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 15 ∧
      threeMarginQ 15 < (251:ℚ)/1000000 := by
  rw [margin15_exact]
  norm_num

theorem margin15_positive : 0 < threeMarginQ 15 := by
  have h := margin15_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
