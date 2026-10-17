import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin13_exact :
    threeMarginQ 13 = (19929758036126629:ℚ)/79716150000000000000 := by
  decide +kernel

theorem margin13_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 13 ∧
      threeMarginQ 13 < (251:ℚ)/1000000 := by
  rw [margin13_exact]
  norm_num

theorem margin13_positive : 0 < threeMarginQ 13 := by
  have h := margin13_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
