import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin02_exact :
    threeMarginQ 2 = (30910970603109972096383:ℚ)/23808556800000000000000 := by
  decide +kernel

theorem margin02_floor :
    (1298313:ℚ)/1000000 ≤ threeMarginQ 2 ∧
      threeMarginQ 2 < (1298314:ℚ)/1000000 := by
  rw [margin02_exact]
  norm_num

theorem margin02_positive : 0 < threeMarginQ 2 := by
  have h := margin02_floor.1
  have hp : (0:ℚ)<1298313/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
