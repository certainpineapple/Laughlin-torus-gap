import torus.shared.FermionCertificateThreeArithmetic

/-! One exact original-row arithmetic leaf. The two inequalities certify
precisely the printed integer floor, using kernel reduction of the actual
rational formula and frozen rows. No native evaluator is used. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling

theorem margin04_exact :
    threeMarginQ 4 = (7546741008522095438231:ℚ)/35712835200000000000000 := by
  decide +kernel

theorem margin04_floor :
    (211317:ℚ)/1000000 ≤ threeMarginQ 4 ∧
      threeMarginQ 4 < (211318:ℚ)/1000000 := by
  rw [margin04_exact]
  norm_num

theorem margin04_positive : 0 < threeMarginQ 4 := by
  have h := margin04_floor.1
  have hp : (0:ℚ)<211317/1000000 := by norm_num
  exact hp.trans_le h

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
