import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin05_exact :
    threeMarginQ 5 = (353876907460004129:ℚ)/1417176000000000000000 := by
  decide +kernel

theorem margin05_floor :
    (249:ℚ)/1000000 ≤ threeMarginQ 5 ∧
      threeMarginQ 5 < (250:ℚ)/1000000 := by
  rw [margin05_exact]
  norm_num

theorem margin05_positive : 0 < threeMarginQ 5 := by
  have h := margin05_floor.1
  have hp : (0:ℚ)<249/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
