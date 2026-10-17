import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin06_exact :
    threeMarginQ 6 = (26650275529068337:ℚ)/106288200000000000000 := by
  decide +kernel

theorem margin06_floor :
    (250:ℚ)/1000000 ≤ threeMarginQ 6 ∧
      threeMarginQ 6 < (251:ℚ)/1000000 := by
  rw [margin06_exact]
  norm_num

theorem margin06_positive : 0 < threeMarginQ 6 := by
  have h := margin06_floor.1
  have hp : (0:ℚ)<250/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
