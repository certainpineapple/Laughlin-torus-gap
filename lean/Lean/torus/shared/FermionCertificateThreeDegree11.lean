import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin11_exact :
    threeMarginQ 11 = (11625103382873:ℚ)/46501087500000000 := by
  decide +kernel

theorem margin11_floor :
    (249:ℚ)/1000000 ≤ threeMarginQ 11 ∧
      threeMarginQ 11 < (250:ℚ)/1000000 := by
  rw [margin11_exact]
  norm_num

theorem margin11_positive : 0 < threeMarginQ 11 := by
  have h := margin11_floor.1
  have hp : (0:ℚ)<249/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
