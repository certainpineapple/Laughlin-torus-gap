import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin09_exact :
    threeMarginQ 9 = (2790351684791537:ℚ)/11160261000000000000 := by
  decide +kernel

theorem margin09_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 9 ∧
      threeMarginQ 9 < (251:ℚ)/1000000 := by
  rw [margin09_exact]
  norm_num

theorem margin09_positive : 0 < threeMarginQ 9 := by
  have h := margin09_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
