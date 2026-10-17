import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin08_exact :
    threeMarginQ 8 = (124419886955963507:ℚ)/496011600000000000000 := by
  decide +kernel

theorem margin08_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 8 ∧
      threeMarginQ 8 < (251:ℚ)/1000000 := by
  rw [margin08_exact]
  norm_num

theorem margin08_positive : 0 < threeMarginQ 8 := by
  have h := margin08_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
