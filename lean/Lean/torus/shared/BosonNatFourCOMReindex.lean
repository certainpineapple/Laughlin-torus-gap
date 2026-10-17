import torus.shared.BosonNatFourMatrixCOMTrace

/-! Reindex a finite degree triangle by relative degree and COM level.
This is a finite sum identity; it carries no spectral or completeness premise. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourCOMReindex
open scoped BigOperators

/-- Total degree / relative degree and relative degree / COM level are the
same finite triangle, including the zero and top-degree boundaries. -/
def degreeCOMEquiv (K : ℕ) :
    (Σ D : Fin (K+1), Fin (D.val+1)) ≃
      (Σ d : Fin (K+1), Fin (K+1-d.val)) where
  toFun x := ⟨⟨x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩,
    ⟨x.1.val-x.2.val, by change x.1.val-x.2.val < K+1-x.2.val; have := x.1.isLt; have := x.2.isLt; omega⟩⟩
  invFun x := ⟨⟨x.1.val+x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩,
    ⟨x.1.val, by change x.1.val < x.1.val+x.2.val+1; omega⟩⟩
  left_inv := by
    rintro ⟨D,d⟩
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      have := d.isLt
      omega
    · apply (Fin.heq_ext_iff (by dsimp; have := d.isLt; omega)).2
      rfl
  right_inv := by
    rintro ⟨d,n⟩
    apply Sigma.ext
    · rfl
    · apply (Fin.heq_ext_iff (by rfl)).2
      dsimp
      omega

/-- Keep every entry in the degree triangle while moving the COM sum inward. -/
theorem sum_degree_COM_reindex (K : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ D : Fin (K+1), ∑ d : Fin (D.val+1), F d.val (D.val-d.val)) =
      ∑ d : Fin (K+1), ∑ n : Fin (K+1-d.val), F d.val n.val := by
  have h := Fintype.sum_equiv (degreeCOMEquiv K)
    (fun x => F x.2.val (x.1.val-x.2.val))
    (fun x => F x.1.val x.2.val) (fun _ => rfl)
  simpa only [Fintype.sum_sigma] using h

/-- Equal COM levels at fixed total degree force the same relative degree,
while retaining every pair of relative multiplicity labels. -/
theorem sum_equal_COM_level (D : ℕ) (r : Fin (D+1) → ℕ)
    (F : (Σ d : Fin (D+1), Fin (r d)) →
      (Σ d : Fin (D+1), Fin (r d)) → ℂ) :
    (∑ i, ∑ j, if D-i.1.val=D-j.1.val then F i j else 0) =
      ∑ d, ∑ a : Fin (r d), ∑ b : Fin (r d), F ⟨d,a⟩ ⟨d,b⟩ := by
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single d]
  · simp only [ite_true]
  · intro e he hne
    have h : D-d.val ≠ D-e.val := by
      intro h
      have hd' := d.isLt
      have he' := e.isLt
      have hv : d.val=e.val := by omega
      exact hne (Fin.ext hv.symm)
    simp only [h,ite_false,Finset.sum_const_zero]
  · simp

#print axioms sum_degree_COM_reindex
#print axioms sum_equal_COM_level
end TorusLean.Shared.BosonNatFourCOMReindex
