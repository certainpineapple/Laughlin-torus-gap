import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin07_exact :
    threeMarginQ 7 = (46496571968306777:ℚ)/186004350000000000000 := by
  decide +kernel

theorem margin07_floor :
    (249:ℚ)/1000000 ≤ threeMarginQ 7 ∧
      threeMarginQ 7 < (250:ℚ)/1000000 := by
  rw [margin07_exact]
  norm_num

theorem margin07_positive : 0 < threeMarginQ 7 := by
  have h := margin07_floor.1
  have hp : (0:ℚ)<249/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
