import torus.shared.BosonFiniteCertificateNatDegreeOrthogonality

/-! Genuine finite weighted-degree components of the original Nat core.
The actual COM lowering commutes with the shifted component projection,
including a separate proof at degree zero, where the zero orbital remains. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

def natOrbitalComponent (d : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  MvPolynomial.weightedHomogeneousComponent id d

theorem natOrbitalComponent_weighted (d : ℕ) (f : Core ℕ ℂ) :
    (natOrbitalComponent d f).IsWeightedHomogeneous id d :=
  MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d f

theorem natOrbitalComponent_particle (N d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous N) : (natOrbitalComponent d f).IsHomogeneous N := by
  intro n hn
  have hc : f.coeff n ≠ 0 := by
    intro h
    apply hn
    simp only [natOrbitalComponent, MvPolynomial.coeff_weightedHomogeneousComponent, h, ite_self]
  exact hN hc

/-- Every polynomial is reconstructed from its actual finite set of weights. -/
theorem natOrbitalComponent_finite_sum (f : Core ℕ ℂ) :
    (∑ d ∈ f.support.image (Finsupp.weight id), natOrbitalComponent d f) = f := by
  classical
  ext n
  simp only [MvPolynomial.coeff_sum, natOrbitalComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight id n)]
  · simp
  · intro e he hen
    simp [Ne.symm hen]
  · intro hn
    have hc : f.coeff n = 0 := by
      by_contra hc
      exact hn (Finset.mem_image.mpr ⟨n, MvPolynomial.mem_support_iff.mpr hc, rfl⟩)
    simp [hc]

theorem nat_annihilate_above_weight (i d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) (hdi : d < i) : annihilate i f = 0 := by
  ext n
  have hz : f.coeff (n+Finsupp.single i 1)=0 := by
    by_contra hc
    have hh := hd hc
    simp only [map_add, Finsupp.weight_single, one_smul, id_eq] at hh
    omega
  change (MvPolynomial.pderiv i f).coeff n=0
  simp only [MvPolynomial.coeff_pderiv, hz, zero_mul, MvPolynomial.coeff_zero]

/-- The actual one-step lowering term shifts the component index by one. -/
theorem natOrbitalComponent_lower_step (d j : ℕ) (f : Core ℕ ℂ) :
    natOrbitalComponent d (create j (annihilate (j+1) f)) =
      create j (annihilate (j+1) (natOrbitalComponent (d+1) f)) := by
  classical
  ext n
  simp only [natOrbitalComponent, MvPolynomial.coeff_weightedHomogeneousComponent,
    create, LinearMap.mulLeft_apply, annihilate, Derivation.coeFn_coe,
    MvPolynomial.coeff_X_mul', MvPolynomial.coeff_pderiv]
  by_cases hn : j ∈ n.support
  · have hw := Finsupp.weight_sub_single_add (w := id) (Finsupp.mem_support_iff.mp hn)
    have hweight : Finsupp.weight id ((n-Finsupp.single j 1)+Finsupp.single (j+1) 1) =
        Finsupp.weight id n + 1 := by
      simp only [map_add, Finsupp.weight_single, one_smul, id_eq]
      dsimp only [id_eq] at hw
      omega
    simp only [hn, ite_eq_left, hweight, Nat.add_right_cancel_iff]
    split_ifs <;> simp
  · simp [hn]

theorem canonicalCOMLowerNat_orbitalComponent_succ (d : ℕ) (f : Core ℕ ℂ) :
    canonicalCOMLowerNat (natOrbitalComponent (d+1) f) =
      natOrbitalComponent d (canonicalCOMLowerNat f) := by
  classical
  let q := natOrbitalComponent (d+1) f
  let m := (f.vars ∪ q.vars).sup id + 1
  have hf : f.vars ⊆ Finset.range (m+1) := by
    intro i hi
    have h := Finset.mem_range.mp (Finset.subset_range_sup_succ (f.vars ∪ q.vars)
      (Finset.mem_union_left _ hi))
    exact Finset.mem_range.mpr (by omega)
  have hq : q.vars ⊆ Finset.range (m+1) := by
    intro i hi
    have h := Finset.mem_range.mp (Finset.subset_range_sup_succ (f.vars ∪ q.vars)
      (Finset.mem_union_right _ hi))
    exact Finset.mem_range.mpr (by omega)
  rw [canonicalCOMLowerNat_finite_sum m _ hq, canonicalCOMLowerNat_finite_sum m _ hf]
  simp only [q, map_sum, map_smul, natOrbitalComponent_lower_step]

/-- Weight zero may contain powers of X 0; its genuine lowering is still zero. -/
theorem canonicalCOMLowerNat_orbitalComponent_zero (f : Core ℕ ℂ) :
    canonicalCOMLowerNat (natOrbitalComponent 0 f) = 0 := by
  classical
  let q := natOrbitalComponent 0 f
  let m := q.vars.sup id + 1
  have hq : q.vars ⊆ Finset.range (m+1) := by
    intro i hi
    have h := Finset.mem_range.mp (Finset.subset_range_sup_succ q.vars hi)
    exact Finset.mem_range.mpr (by omega)
  rw [canonicalCOMLowerNat_finite_sum m _ hq]
  apply Finset.sum_eq_zero
  intro j _
  rw [nat_annihilate_above_weight (j+1) 0 _ (natOrbitalComponent_weighted 0 f) (by omega),
    map_zero, smul_zero]

/-- Every genuine weighted-degree component of an actual relative vacuum
is still a vacuum for the original lowering derivation. -/
theorem natOrbitalComponent_lower_kernel (d : ℕ) (f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) : canonicalCOMLowerNat (natOrbitalComponent d f)=0 := by
  cases d with
  | zero => exact canonicalCOMLowerNat_orbitalComponent_zero f
  | succ d => rw [canonicalCOMLowerNat_orbitalComponent_succ, hL, map_zero]

#print axioms natOrbitalComponent_finite_sum
#print axioms natOrbitalComponent_lower_step
#print axioms canonicalCOMLowerNat_orbitalComponent_zero
#print axioms natOrbitalComponent_lower_kernel
end TorusLean.BosonFiniteCertificate
