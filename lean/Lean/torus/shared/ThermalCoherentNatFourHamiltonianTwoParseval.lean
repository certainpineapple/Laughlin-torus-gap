import torus.shared.BosonFiniteCertificateNatOccupationInner
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Complete ordered two-particle resolution on natural orbital labels

At fixed orbital weight `t`, every genuine particle-degree-two occupation is
`single a 1 + single b 1` with `a+b=t`.  The ordered words `X j * X (t-j)`
therefore give a complete finite tight frame in the positive factorial
occupation metric.  Both orders are retained, and the coincident-label word
has its actual occupation weight `2!`; the common frame factor is `1/2`.

This is the `N=2` output sector in `Core ℕ ℂ`, for arbitrary `t`.  It does not
replace this sector by degree `t` in two variables, or assume completeness,
nondegeneracy, an orbital cutoff, or a Hamiltonian identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators ComplexConjugate

/-- A true degree-two occupation consists of two orbital labels, with
repetitions allowed. No finite orbital enumeration is used. -/
theorem nat_occupation_degree_two_word (n : ℕ →₀ ℕ) (hN : n.degree = 2) :
    ∃ a b, n = Finsupp.single a 1 + Finsupp.single b 1 := by
  classical
  obtain ⟨u, hu, hu1⟩ := Finsupp.exists_le_degree_eq n 1 (by omega)
  obtain ⟨v, huv⟩ := le_iff_exists_add.mp hu
  have hv : v.degree = 1 := by
    have h := congrArg Finsupp.degree huv
    simp only [map_add, hN, hu1] at h
    omega
  have eu : u ∈ Set.range (fun a : ℕ => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]
    exact hu1
  have ev : v ∈ Set.range (fun b : ℕ => Finsupp.single b 1) := by
    rw [Finsupp.range_single_one]
    exact hv
  obtain ⟨a, rfl⟩ := eu
  obtain ⟨b, rfl⟩ := ev
  exact ⟨a, b, huv⟩

private theorem inner_X_left (j : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (MvPolynomial.X j) f = f.coeff (Finsupp.single j 1) := by
  simp [MvPolynomial.X, natOccupationInner_monomial_left, natOccupationWeight]

private theorem inner_X_X (a b : ℕ) :
    natOccupationInner (MvPolynomial.X a : Core ℕ ℂ) (MvPolynomial.X b) =
      if a = b then 1 else 0 := by
  classical
  rw [inner_X_left]
  simp [MvPolynomial.X, Finsupp.single_eq_single_iff, eq_comm]

/-- The actual two-word Gram entries count the two ordered contractions.
For `a=b=j` the right side is `2`, as required by the factorial metric. -/
theorem nat_two_ordered_gram (a b j : ℕ) :
    natOccupationInner
      (MvPolynomial.X j * MvPolynomial.X (a + b - j) : Core ℕ ℂ)
      (MvPolynomial.X a * MvPolynomial.X b) =
        (if j = a then 1 else 0) + (if j = b then 1 else 0) := by
  classical
  change natOccupationInner (create j (MvPolynomial.X (a + b - j)))
    (MvPolynomial.X a * MvPolynomial.X b) = _
  rw [nat_create_adjoint]
  by_cases ha : j = a
  · subst j
    by_cases hab : a = b
    · subst b
      simp [annihilate, MvPolynomial.pderiv_mul,
        natOccupationInner_add_right, inner_X_X]
    · simp [annihilate, MvPolynomial.pderiv_mul, hab, Ne.symm hab, inner_X_X]
  · by_cases hb : j = b
    · subst j
      simp [annihilate, MvPolynomial.pderiv_mul, ha, Ne.symm ha, inner_X_X]
    · simp [annihilate, MvPolynomial.pderiv_mul, ha, Ne.symm ha, hb, Ne.symm hb,
        natOccupationInner_zero_right]

private def twoResolution (t : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (1 / 2 : ℂ) • ∑ j ∈ Finset.range (t + 1),
    { toFun := fun f =>
        natOccupationInner (MvPolynomial.X j * MvPolynomial.X (t - j)) f •
          (MvPolynomial.X j * MvPolynomial.X (t - j))
      map_add' := by
        intro f g
        rw [natOccupationInner_add_right, add_smul]
      map_smul' := by
        intro c f
        simp only [natOccupationInner_smul_right, smul_smul, RingHom.id_apply] }

private theorem twoResolution_apply (t : ℕ) (f : Core ℕ ℂ) :
    twoResolution t f =
      (1 / 2 : ℂ) • ∑ j ∈ Finset.range (t + 1),
        natOccupationInner (MvPolynomial.X j * MvPolynomial.X (t - j)) f •
          (MvPolynomial.X j * MvPolynomial.X (t - j)) := by
  simp only [twoResolution, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

private theorem twoResolution_word (a b : ℕ) :
    twoResolution (a + b) (MvPolynomial.X a * MvPolynomial.X b) =
      (MvPolynomial.X a * MvPolynomial.X b : Core ℕ ℂ) := by
  classical
  rw [twoResolution_apply]
  have hterm (j : ℕ) :
      natOccupationInner
          (MvPolynomial.X j * MvPolynomial.X (a + b - j) : Core ℕ ℂ)
          (MvPolynomial.X a * MvPolynomial.X b) •
        (MvPolynomial.X j * MvPolynomial.X (a + b - j)) =
      (if j = a then (MvPolynomial.X a * MvPolynomial.X b : Core ℕ ℂ) else 0) +
        (if j = b then (MvPolynomial.X a * MvPolynomial.X b : Core ℕ ℂ) else 0) := by
    rw [nat_two_ordered_gram, add_smul]
    congr 1
    · by_cases h : j = a <;> simp [h]
    · by_cases h : j = b <;> simp [h, mul_comm]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have ha : a ∈ Finset.range (a + b + 1) := Finset.mem_range.mpr (by omega)
  have hb : b ∈ Finset.range (a + b + 1) := Finset.mem_range.mpr (by omega)
  simp only [Finset.sum_ite_eq', ha, hb, ↓reduceIte]
  rw [← two_smul ℂ, smul_smul]
  norm_num

/-- Full finite reconstruction of every actual `N=2`, orbital-weight-`t`
polynomial. The sum keeps all ordered labels and the diagonal multiplicity. -/
theorem nat_two_ordered_parseval (t : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 2) (hd : f.IsWeightedHomogeneous id t) :
    f = (1 / 2 : ℂ) • ∑ j ∈ Finset.range (t + 1),
      natOccupationInner (MvPolynomial.X j * MvPolynomial.X (t - j)) f •
        (MvPolynomial.X j * MvPolynomial.X (t - j)) := by
  classical
  rw [← twoResolution_apply]
  rw [← MvPolynomial.support_sum_monomial_coeff f, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 2 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  obtain ⟨a, b, he⟩ := nat_occupation_degree_two_word n hdeg
  have ht : a + b = t := by
    simpa only [he, map_add, Finsupp.weight_single, one_smul, id_eq] using hd hc
  have hm : MvPolynomial.monomial n (f.coeff n) =
      f.coeff n • (MvPolynomial.X a * MvPolynomial.X b) := by
    simp [he, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.smul_monomial, smul_eq_mul]
  rw [hm, map_smul, ← ht, twoResolution_word]

/-- Complex cross Parseval in the actual positive occupation form. Only the
first argument needs the sector hypotheses; the second may be any core vector. -/
theorem nat_two_ordered_cross_parseval (t : ℕ) (f g : Core ℕ ℂ)
    (hN : f.IsHomogeneous 2) (hd : f.IsWeightedHomogeneous id t) :
    natOccupationInner f g = (1 / 2 : ℂ) * ∑ j ∈ Finset.range (t + 1),
      star (natOccupationInner (MvPolynomial.X j * MvPolynomial.X (t - j)) f) *
        natOccupationInner (MvPolynomial.X j * MvPolynomial.X (t - j)) g := by
  conv_lhs => rw [nat_two_ordered_parseval t f hN hd]
  rw [natOccupationInner_smul_left, natOccupationInner_sum_left]
  simp only [natOccupationInner_smul_left]
  norm_num

#print axioms nat_occupation_degree_two_word
#print axioms nat_two_ordered_gram
#print axioms nat_two_ordered_parseval
#print axioms nat_two_ordered_cross_parseval
end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
