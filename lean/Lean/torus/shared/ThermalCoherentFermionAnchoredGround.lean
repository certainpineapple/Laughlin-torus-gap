import torus.shared.ThermalCoherentFermionAnchoredHamiltonian
import torus.shared.ThermalCoherentFermionAnchoredWeights

/-! The actual (0,1) identity subtraction and the two surviving anchored
fermionic columns. Both the ground sign and the two factorial coefficients
are proved from the original finite coefficient creator. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open OAI.Laughlin.Fock TorusLean.Fermion
open TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators

private theorem planePairCoefficient_zero_matrix (i j : ℕ) :
    planePairCoefficient 0 i j =
      if i=0 ∧ j=1 then -1 else if i=1 ∧ j=0 then 1 else 0 := by
  by_cases h : i+j=1
  · have he : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      norm_num [planePairCoefficient,paperPairWeight]
  · have h01 : ¬(i=0 ∧ j=1) := by omega
    have h10 : ¬(i=1 ∧ j=0) := by omega
    simp only [planePairCoefficient,h,h01,h10,ite_false]

private theorem rawPairCreate_swap (Q : ℕ) (a b : Orbital Q) :
    rawPairCreate Q b a = -rawPairCreate Q a b := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ b*(ExteriorAlgebra.ι ℂ a*x) =
    -(ExteriorAlgebra.ι ℂ a*(ExteriorAlgebra.ι ℂ b*x))
  have hs : ExteriorAlgebra.ι ℂ b*ExteriorAlgebra.ι ℂ a =
      -(ExteriorAlgebra.ι ℂ a*ExteriorAlgebra.ι ℂ b) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a)
  rw [← mul_assoc,hs,neg_mul,mul_assoc]

/-- The original m=1 pair ground creator is -a0†a1†, exactly. -/
theorem planePairCreate_ground (Q : ℕ) (a b : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) :
    planePairCreate Q 0 = -rawPairCreate Q (mode a) (mode b) := by
  classical
  have hab : a≠b := by intro h; have := congrArg Fin.val h; omega
  have h0 (i : Fin (Q+1)) : i.val=0 ↔ i=a := by
    constructor
    · intro hi; apply Fin.ext; omega
    · rintro rfl; exact ha
  have h1 (i : Fin (Q+1)) : i.val=1 ↔ i=b := by
    constructor
    · intro hi; apply Fin.ext; omega
    · rintro rfl; exact hb
  have hc (i j : Fin (Q+1)) : (planePairCoefficient 0 i.val j.val:ℂ) =
      -(if i=a ∧ j=b then 1 else 0)+(if i=b ∧ j=a then 1 else 0) := by
    rw [planePairCoefficient_zero_matrix]
    simp only [h0,h1]
    by_cases hij : i=a ∧ j=b
    · rcases hij with ⟨rfl,rfl⟩
      simp [hab,Ne.symm hab]
    · by_cases hji : i=b ∧ j=a
      · rcases hji with ⟨rfl,rfl⟩
        simp [hab,Ne.symm hab]
      · simp [hij,hji]
  have hs : (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
      (planePairCoefficient 0 i.val j.val:ℂ) • rawPairCreate Q (mode i) (mode j)) =
      -rawPairCreate Q (mode a) (mode b)+rawPairCreate Q (mode b) (mode a) := by
    simp [hc,add_smul,Finset.sum_add_distrib,ite_and]
  rw [planePairCreate,coefficientPairCreate,hs,
    rawPairCreate_swap Q (mode a) (mode b)]
  module

/-- The p=0 contribution really is the subtracted identity on the anchor. -/
theorem planePairCreate_ground_anchor (Q : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) :
    -planePairCreate Q 0 (rawCreate Q (mode d) 1) =
      rawTripleVector Q (mode a) (mode b) (mode d) := by
  rw [planePairCreate_ground Q a b ha hb,LinearMap.neg_apply,neg_neg]
  rfl

/-- The original connected column with both exact CAR signs. It is valid
only after all actual occupied channels are in the H cutoff, and requires
l>=2 for the nonrepeated canonical anchor interpretation. -/
theorem planePairHamiltonian_connected_anchor (Q D : ℕ)
    (a b d : Fin (Q+1)) (ha : a.val=0) (hb : b.val=1)
    (hl : 1<d.val) (hD : d.val≤D) :
    (planePairHamiltonian Q D-1) (rawTripleVector Q (mode a) (mode b) (mode d)) =
      (Real.sqrt (d.val:ℝ)/(Real.sqrt (2:ℝ))^(d.val-1):ℂ) •
        planePairCreate Q (d.val-1) (rawCreate Q (mode b) 1) -
      (((d.val:ℝ)-1)/(Real.sqrt (2:ℝ))^d.val:ℂ) •
        planePairCreate Q d.val (rawCreate Q (mode a) 1) := by
  have h0 := planePairCreate_ground_anchor Q a b d ha hb
  have hα := anchored_zero_pair_weight (d.val-1)
  have hd : d.val-1+1=d.val := by omega
  have hcast : ((d.val-1:ℕ):ℝ)+1=(d.val:ℝ) := by exact_mod_cast hd
  rw [hd,hcast] at hα
  have hαC := congrArg (fun r : ℝ => (r:ℂ)) hα
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow] at hαC
  have hβ := anchored_one_pair_weight d.val
  simp only [LinearMap.sub_apply,Module.End.one_apply]
  rw [planePairHamiltonian_anchored_three_channels Q D a b d ha hb hl hD,h0]
  rw [hαC,hβ]
  simp only [inv_pow,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_pow]
  module


private theorem vectorAnnihilate_mode (Q : ℕ) (i : Fin (Q+1)) :
    vectorAnnihilate Q (mode i)=annihilate i := by
  classical
  apply LinearMap.ext
  intro x
  rw [vectorAnnihilate_sum]
  simp [mode,Pi.single_apply]

/-- Literal number operators are creation followed by the correct ordered
pair removal. The sign cancellation uses two genuine CAR identities. -/
theorem anchoredNumber_eq_pair (Q : ℕ) (a b : Fin (Q+1)) (hab : a≠b) :
    anchoredNumber Q a b = rawPairCreate Q (mode a) (mode b) *
      rawPairAnnihilate Q (mode a) (mode b) := by
  have hm := mixed_car a b
  simp only [if_neg hab,zero_smul] at hm
  have ha := annihilate_anticommute a b
  have hmc : annihilate a*create b=-(create b*annihilate a) :=
    eq_neg_of_add_eq_zero_left hm
  have hac : annihilate a*annihilate b=-(annihilate b*annihilate a) :=
    eq_neg_of_add_eq_zero_left ha
  simp only [anchoredNumber,rawPairCreate,rawPairAnnihilate,vectorAnnihilate_mode]
  change (create a*annihilate a)*(create b*annihilate b) =
    (create a*create b)*(annihilate b*annihilate a)
  calc
    _ = create a*(annihilate a*create b)*annihilate b := by noncomm_ring
    _ = -(create a*create b)*(annihilate a*annihilate b) := by
      rw [hmc]
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply,LinearMap.neg_apply,map_neg]
    _ = _ := by
      rw [hac]
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply,LinearMap.neg_apply,map_neg,neg_neg]

private theorem anchored_pair_contraction_mem (Q : ℕ) (a b d x y z : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hdeg : x.val+y.val+z.val=d.val+1) :
    rawPairGram Q (mode a) (mode b) (mode x) (mode y) • rawCreate Q (mode z) 1 ∈
      Submodule.span ℂ {rawCreate Q (mode d) 1} := by
  classical
  by_cases hxy : x=a ∧ y=b
  · rcases hxy with ⟨rfl,rfl⟩
    have hz : z=d := Fin.ext (by omega)
    subst z
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · by_cases hyx : x=b ∧ y=a
    · rcases hyx with ⟨rfl,rfl⟩
      have hz : z=d := Fin.ext (by omega)
      subst z
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have hzero : rawPairGram Q (mode a) (mode b) (mode x) (mode y)=0 := by
        simp only [rawPairGram,rawGram_mode]
        by_cases hax : a=x <;> by_cases hby : b=y <;>
          by_cases hbx : b=x <;> by_cases hay : a=y <;> simp_all
      rw [hzero,zero_smul]
      exact Submodule.zero_mem _

/-- On the true L=l+1 block, removing modes 0 and 1 leaves only mode l.
This is a support theorem for the existing exterior algebra. -/
theorem rawPairAnnihilate_anchor_range (Q : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (f : Space Q)
    (hf : f∈threeDegreeSpan Q (d.val+1)) :
    rawPairAnnihilate Q (mode a) (mode b) f ∈
      Submodule.span ℂ {rawCreate Q (mode d) 1} := by
  have hk : threeDegreeSpan Q (d.val+1) ≤
      Submodule.comap (rawPairAnnihilate Q (mode a) (mode b))
        (Submodule.span ℂ {rawCreate Q (mode d) 1}) := by
    apply Submodule.span_le.mpr
    rintro g ⟨x,y,z,hd,rfl⟩
    change rawPairAnnihilate Q (mode a) (mode b)
      (rawTripleVector Q (mode x) (mode y) (mode z)) ∈
        (Submodule.span ℂ {rawCreate Q (mode d) 1} : Submodule ℂ (Space Q))
    rw [rawPairAnnihilate_tripleVector]
    exact Submodule.add_mem _
      (Submodule.sub_mem _ (anchored_pair_contraction_mem Q a b d x y z ha hb hd)
        (anchored_pair_contraction_mem Q a b d x z y ha hb (by omega)))
      (anchored_pair_contraction_mem Q a b d y z x ha hb (by omega))
  exact hk hf

private theorem rawSingle_inner_self (Q : ℕ) (d : Fin (Q+1)) :
    occupationInner Q (rawCreate Q (mode d) 1) (rawCreate Q (mode d) 1)=1 := by
  rw [rawCreate_adjoint,raw_annihilate_create_apply,raw_annihilate_vacuum]
  simp only [rawGram_mode,if_true,one_smul,map_zero,sub_zero,occupationInner_vacuum]

/-- The actual n0*n1 is rank one on the actual three-particle L=l+1 block.
The formula remains valid for l=0,1, where its wedge is literally zero. -/
theorem anchoredNumber_threeDegreeSpan_rank_one (Q : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (f : Space Q)
    (hf : f∈threeDegreeSpan Q (d.val+1)) :
    anchoredNumber Q a b f =
      occupationInner Q (rawTripleVector Q (mode a) (mode b) (mode d)) f •
        rawTripleVector Q (mode a) (mode b) (mode d) := by
  have hab : a≠b := by intro h; have := congrArg Fin.val h; omega
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    (rawPairAnnihilate_anchor_range Q a b d ha hb f hf)
  have hi : occupationInner Q (rawTripleVector Q (mode a) (mode b) (mode d)) f=c := by
    change occupationInner Q
      (rawPairCreate Q (mode a) (mode b) (rawCreate Q (mode d) 1)) f=c
    rw [rawPairCreate_adjoint,← hc,occupationInner_smul_right,rawSingle_inner_self,mul_one]
  rw [anchoredNumber_eq_pair Q a b hab,Module.End.mul_apply,← hc,map_smul,hi]
  rfl

private theorem connected_selfAdjoint (Q D : ℕ) (x y : Space Q) :
    occupationInner Q ((planePairHamiltonian Q D-1) x) y =
      occupationInner Q x ((planePairHamiltonian Q D-1) y) := by
  simp only [LinearMap.sub_apply,Module.End.one_apply]
  have hl : occupationInner Q (planePairHamiltonian Q D x-x) y =
      occupationInner Q (planePairHamiltonian Q D x) y-occupationInner Q x y := by
    simp only [occupationInner,map_sub,Finsupp.sub_apply,star_sub,sub_mul,
      Finset.sum_sub_distrib]
  have hr : occupationInner Q x (planePairHamiltonian Q D y-y) =
      occupationInner Q x (planePairHamiltonian Q D y)-occupationInner Q x y := by
    simp only [occupationInner,map_sub,Finsupp.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [hl,hr,planePairHamiltonian_selfAdjoint]

/-- Genuine operator rank-one row of K_F=n0*n1*(H_D-I), not a compression
used to define H or an assumed row formula. It uses true degree preservation. -/
theorem planeAnchoredKernel_rank_one (Q D : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (f : Space Q)
    (hf : f∈threeDegreeSpan Q (d.val+1)) :
    planeAnchoredKernel Q D a b f =
      occupationInner Q
        ((planePairHamiltonian Q D-1) (rawTripleVector Q (mode a) (mode b) (mode d))) f •
        rawTripleVector Q (mode a) (mode b) (mode d) := by
  rw [planeAnchoredKernel,Module.End.mul_apply,
    anchoredNumber_threeDegreeSpan_rank_one Q a b d ha hb _
      (planeConnected_threeDegreeSpan Q D (d.val+1) f hf),← connected_selfAdjoint]

/-- The two-column row with exact coefficients and the full actual cutoff.
Q>=l is encoded by d:Fin(Q+1); D>=l is explicit. -/
theorem planeAnchoredKernel_two_column_row (Q D : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hl : 1<d.val) (hD : d.val≤D)
    (f : Space Q) (hf : f∈threeDegreeSpan Q (d.val+1)) :
    planeAnchoredKernel Q D a b f =
      occupationInner Q
        ((Real.sqrt (d.val:ℝ)/(Real.sqrt (2:ℝ))^(d.val-1):ℂ) •
          planePairCreate Q (d.val-1) (rawCreate Q (mode b) 1) -
        (((d.val:ℝ)-1)/(Real.sqrt (2:ℝ))^d.val:ℂ) •
          planePairCreate Q d.val (rawCreate Q (mode a) 1)) f •
        rawTripleVector Q (mode a) (mode b) (mode d) := by
  rw [planeAnchoredKernel_rank_one Q D a b d ha hb f hf,
    planePairHamiltonian_connected_anchor Q D a b d ha hb hl hD]

/-- The repeated low-degree wedges give zero actual K_F rows. -/
theorem planeAnchoredKernel_low_degree_zero (Q D : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hl : d.val≤1)
    (f : Space Q) (hf : f∈threeDegreeSpan Q (d.val+1)) :
    planeAnchoredKernel Q D a b f=0 := by
  rw [planeAnchoredKernel_rank_one Q D a b d ha hb f hf]
  have hd : d=a ∨ d=b := by
    by_cases h : d.val=0
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))
  rcases hd with rfl | rfl
  · rw [rawTripleVector_repeat_first,smul_zero]
  · rw [rawTripleVector_repeat_second,smul_zero]


/-- The ordered half is exactly the original unordered pair creator, for
every p and Q. Antisymmetry, not an orthogonality convention, cancels the half. -/
theorem planePairCreate_unordered (Q p : ℕ) :
    planePairCreate Q p = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
      if i<j then (planePairCoefficient p i.val j.val:ℂ) •
        rawPairCreate Q (mode i) (mode j) else 0 := by
  classical
  have hd (i : Fin (Q+1)) : rawPairCreate Q (mode i) (mode i)=0 := by
    apply LinearMap.ext
    intro x
    change ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode i)*x)=0
    rw [← mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]
  have h := ordered_pair_sum (Finset.univ : Finset (Fin (Q+1)))
    (fun i j => (planePairCoefficient p i.val j.val:ℂ))
    (fun i j => rawPairCreate Q (mode i) (mode j))
    (fun i j => rawPairCreate_swap Q (mode i) (mode j)) hd
  simp only [planePairCreate,coefficientPairCreate,h,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i<j
  · simp only [hij,ite_true]
    rw [planePairCoefficient_antisymm p i.val j.val]
    simp only [Complex.ofReal_neg]
    module
  · simp only [hij,ite_false,smul_zero]

end TorusLean.Shared.ThermalCoherentFermionAnchored
