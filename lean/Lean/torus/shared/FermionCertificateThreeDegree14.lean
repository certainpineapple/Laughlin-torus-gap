import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin14_exact :
    threeMarginQ 14 = (25472378721696121:ℚ)/3936600000000000000 := by
  decide +kernel

theorem margin14_floor :
    (6470:ℚ)/1000000 ≤ threeMarginQ 14 ∧
      threeMarginQ 14 < (6471:ℚ)/1000000 := by
  rw [margin14_exact]
  norm_num

theorem margin14_positive : 0 < threeMarginQ 14 := by
  have h := margin14_floor.1
  have hp : (0:ℚ)<6470/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
