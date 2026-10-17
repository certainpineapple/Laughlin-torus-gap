import torus.shared.BosonNatThreeCOMCellTrace
import torus.shared.BosonFiniteCertificateNatRelativeRankComparison

/-! The COM labels select the unchanged old complete relative source families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeRelativeColumnIdentity
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2 Matrix
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

theorem k300_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨0,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k300natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k300occ (fun i => (b300relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k301_relativeColumn_eq_family :
    (fun a : Fin 0 => natCOMRelativeColumn (⟨1,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k301natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k301occ (fun i => (b301relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k302_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨2,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k302natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k302occ (fun i => (b302relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k303_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨3,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k303natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k303occ (fun i => (b303relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k304_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨4,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k304natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k304occ (fun i => (b304relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k305_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨5,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k305natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k305occ (fun i => (b305relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k306_relativeColumn_eq_family :
    (fun a : Fin 2 => natCOMRelativeColumn (⟨6,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k306natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k306occ (fun i => (b306relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k307_relativeColumn_eq_family :
    (fun a : Fin 1 => natCOMRelativeColumn (⟨7,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k307natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k307occ (fun i => (b307relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

theorem k308_relativeColumn_eq_family :
    (fun a : Fin 2 => natCOMRelativeColumn (⟨8,by decide⟩ : Fin 9)
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) = k308natRelativeFamily := by
  funext a
  change MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ Pi.single a 1)) =
    MvPolynomial.rename Fin.val
    (canonicalBlock (factorialScale 8) k308occ (fun i => (b308relative i a : ℂ)))
  congr 2
  funext i
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexify] <;> fin_cases a <;> simp_all

end TorusLean.Shared.BosonNatThreeRelativeColumnIdentity
