import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin12_exact :
    threeMarginQ 12 = (19930497521112107:ℚ)/79716150000000000000 := by
  decide +kernel

theorem margin12_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 12 ∧
      threeMarginQ 12 < (251:ℚ)/1000000 := by
  rw [margin12_exact]
  norm_num

theorem margin12_positive : 0 < threeMarginQ 12 := by
  have h := margin12_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
