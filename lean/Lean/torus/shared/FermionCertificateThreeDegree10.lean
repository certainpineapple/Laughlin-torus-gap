import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin10_exact :
    threeMarginQ 10 = (17442867967879651:ℚ)/69751631250000000000 := by
  decide +kernel

theorem margin10_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 10 ∧
      threeMarginQ 10 < (251:ℚ)/1000000 := by
  rw [margin10_exact]
  norm_num

theorem margin10_positive : 0 < threeMarginQ 10 := by
  have h := margin10_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
