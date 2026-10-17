import torus.shared.BosonFiniteCertificateNatCOMCompatibility

/-! Restriction of the genuine Nat raising to the already checked finite
operator before its boundary. The no-top-label guard is derived from the
actual N=3 orbital degree, not assumed as an operator equality. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

theorem canonicalCOMRaise9_C (c : ℂ) : canonicalCOMRaise9 (MvPolynomial.C c) = 0 := by
  have hOne : canonicalCOMRaise9 1 = 0 := by
    simpa only [mul_one,one_mul,add_eq_left] using (canonicalCOMRaise9_mul 1 1).symm
  rw [MvPolynomial.C_eq_smul_one,map_smul,hOne,smul_zero]

theorem canonicalCOMRaiseNat_rename_X (j : Fin 9) (hj : j.val<8) :
    canonicalCOMRaiseNat (MvPolynomial.rename Fin.val (MvPolynomial.X j)) =
      MvPolynomial.rename Fin.val (canonicalCOMRaise9 (MvPolynomial.X j)) := by
  let a : Fin 8 := ⟨j.val,hj⟩
  have ha : raiseSource9 a=j := Fin.ext rfl
  have hx := canonicalCOMRaise9_X_source a
  rw [ha] at hx
  rw [MvPolynomial.rename_X,canonicalCOMRaiseNat_X,hx,map_smul,MvPolynomial.rename_X]
  rfl

theorem canonicalCOMRaiseNat_rename_word (s : List (Fin 9))
    (hs : ∀ j ∈ s, j.val<8) :
    canonicalCOMRaiseNat (MvPolynomial.rename Fin.val (wordPolynomial s)) =
      MvPolynomial.rename Fin.val (canonicalCOMRaise9 (wordPolynomial s)) := by
  induction s with
  | nil =>
    have hN : canonicalCOMRaiseNat 1=0 := by simpa only [map_one] using canonicalCOMRaiseNat_C 1
    have hF : canonicalCOMRaise9 1=0 := by simpa only [map_one] using canonicalCOMRaise9_C 1
    simp only [wordPolynomial_nil,map_one,hN,hF,map_zero]
  | cons j s ih =>
    have hj := hs j (List.mem_cons_self)
    have hrest : ∀ a ∈ s, a.val<8 := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    rw [wordPolynomial_cons,map_mul,canonicalCOMRaiseNat_mul,
      canonicalCOMRaiseNat_rename_X j hj,ih hrest,canonicalCOMRaise9_mul,
      map_add,map_mul,map_mul]

/-- Genuine restriction on every homogeneous N=3 polynomial below degree 8. -/
theorem canonicalCOMRaiseNat_rename_homogeneous_three (d : ℕ) (hd8 : d<8)
    (f : Core (Fin 9) ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous Fin.val d) :
    canonicalCOMRaiseNat (MvPolynomial.rename Fin.val f) =
      MvPolynomial.rename Fin.val (canonicalCOMRaise9 f) := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree=3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  obtain ⟨a,b,c,he⟩ := occupation_degree_three_word n hdeg
  have hsum : a.val+b.val+c.val=d := by
    simpa only [he,map_add,Finsupp.weight_single,one_smul] using hd hc
  have hword : wordOccupation [a,b,c]=n := by
    rw [he]
    simp only [wordOccupation,add_zero,add_assoc]
  have hm : MvPolynomial.monomial n (f.coeff n) = (f.coeff n) • wordPolynomial [a,b,c] := by
    rw [wordPolynomial_eq_monomial,hword,MvPolynomial.smul_monomial]
    simp only [smul_eq_mul,mul_one]
  rw [hm,map_smul,map_smul,map_smul,map_smul]
  congr 1
  apply canonicalCOMRaiseNat_rename_word
  intro j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl <;> omega

#print axioms canonicalCOMRaiseNat_rename_homogeneous_three
end TorusLean.BosonFiniteCertificate
