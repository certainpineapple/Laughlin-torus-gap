import torus.shared.ThermalCoherentFermionAnchoredCoefficients

/-! Actual finite plane pair Hamiltonian and anchored number operator.
The Hamiltonian is the sum of the genuine coefficient creators/removers;
the anchored operator is n_a n_b (H-I), in the original exterior algebra.
Its three occupied pair channels are computed before the (0,1) identity
subtraction. No matrix compression or desired rank formula defines H. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open OAI.Laughlin.Fock TorusLean.Fermion
open TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

def planePairHamiltonian (Q D : ℕ) : Module.End ℂ (Space Q) :=
  ∑ p ∈ Finset.range (D+1), planePairCreate Q p * planePairRemove Q p

/-- The literal finite span of true three-mode words of total orbital
level L. Completeness against the degree occupation projector is separate. -/
def threeDegreeSpan (Q L : ℕ) : Submodule ℂ (Space Q) :=
  Submodule.span ℂ {f | ∃ a b d : Fin (Q+1), a.val+b.val+d.val=L ∧
    rawTripleVector Q (mode a) (mode b) (mode d)=f}

/-- Actual two occupied-mode number operators. -/
def anchoredNumber (Q : ℕ) (a b : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  (create a * annihilate a) * (create b * annihilate b)

def planeAnchoredKernel (Q D : ℕ) (a b : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  anchoredNumber Q a b * (planePairHamiltonian Q D - 1)

private theorem occupationInner_conj_symm (Q : ℕ) (x y : Space Q) :
    conj (occupationInner Q x y)=occupationInner Q y x :=
  PhysicalFermionNormalSquare.occupationInner_star Q x y

/-- The original finite H has its true complex cross form. -/
theorem planePairHamiltonian_cross (Q D : ℕ) (x y : Space Q) :
    occupationInner Q (planePairHamiltonian Q D x) y =
      ∑ p ∈ Finset.range (D+1), occupationInner Q
        (planePairRemove Q p x) (planePairRemove Q p y) := by
  simp only [planePairHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,planePairCreate_adjoint]

/-- Genuine all-Core self-adjointness, used to turn the computed H q column
into the anchored bra. -/
theorem planePairHamiltonian_selfAdjoint (Q D : ℕ) (x y : Space Q) :
    occupationInner Q (planePairHamiltonian Q D x) y =
      occupationInner Q x (planePairHamiltonian Q D y) := by
  have h := congrArg conj (planePairHamiltonian_cross Q D y x)
  simp only [map_sum,occupationInner_conj_symm] at h
  exact (planePairHamiltonian_cross Q D x y).trans h.symm

/-- Genuine high-channel vanishing on every finite combination of
three-mode words in the stated orbital block. -/
theorem planePairRemove_threeDegreeSpan_high_zero (Q L p : ℕ) (hp : L≤p)
    (f : Space Q) (hf : f∈threeDegreeSpan Q L) : planePairRemove Q p f=0 := by
  have hk : threeDegreeSpan Q L≤LinearMap.ker (planePairRemove Q p) := by
    apply Submodule.span_le.mpr
    rintro g ⟨a,b,d,hd,rfl⟩
    exact planePairRemove_triple_high_zero Q p a b d (by omega)
  exact hk hf

/-- Once all genuine degree-L channels are included, extending the H sum
changes no action on the stated source block. No zero tail is assumed. -/
theorem planePairHamiltonian_cutoff_stable (Q L D E : ℕ) (hD : L≤D+1)
    (hDE : D≤E) (f : Space Q) (hf : f∈threeDegreeSpan Q L) :
    planePairHamiltonian Q D f=planePairHamiltonian Q E f := by
  simp only [planePairHamiltonian,LinearMap.sum_apply,Module.End.mul_apply]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro p hpE hpD
  have hp : L≤p := by
    have hnp : ¬p<D+1 := by simpa only [Finset.mem_range] using hpD
    omega
  rw [planePairRemove_threeDegreeSpan_high_zero Q L p hp f hf,map_zero]

/-- The complete literal anchored column. Only p=0,l-1,l survive. The
cutoff includes all three channels; orbital labels are genuine Fin indices. -/
theorem planePairHamiltonian_anchored_three_channels (Q D : ℕ)
    (a b d : Fin (Q+1)) (ha : a.val=0) (hb : b.val=1)
    (hl : 1<d.val) (hD : d.val≤D) :
    planePairHamiltonian Q D (rawTripleVector Q (mode a) (mode b) (mode d)) =
      -planePairCreate Q 0 (rawCreate Q (mode d) 1) +
      ((d.val:ℝ)*paperPairWeight (d.val-1) 0 d.val : ℂ) •
        planePairCreate Q (d.val-1) (rawCreate Q (mode b) 1) +
      ((1-(d.val:ℝ))*paperPairWeight d.val 1 d.val : ℂ) •
        planePairCreate Q d.val (rawCreate Q (mode a) 1) := by
  classical
  have h0 : (∑ p ∈ Finset.range (D+1), ((if p=0 then -1 else 0):ℂ) •
      planePairCreate Q p (rawCreate Q (mode d) 1)) =
      -planePairCreate Q 0 (rawCreate Q (mode d) 1) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro p hp hp0
      simp [hp0]
    · simp
  have h1 : (∑ p ∈ Finset.range (D+1),
      ((if d.val=p+1 then -(d.val:ℝ)*paperPairWeight p 0 d.val else 0):ℂ) •
        planePairCreate Q p (rawCreate Q (mode b) 1)) =
      (-(d.val:ℝ)*paperPairWeight (d.val-1) 0 d.val : ℂ) •
        planePairCreate Q (d.val-1) (rawCreate Q (mode b) 1) := by
    rw [Finset.sum_eq_single (d.val-1)]
    · rw [if_pos (show d.val=d.val-1+1 by omega)]
    · intro p hp hne
      have h : d.val≠p+1 := by omega
      simp only [h,if_false,Complex.ofReal_zero,zero_smul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have h2 : (∑ p ∈ Finset.range (D+1),
      ((if d.val=p then (1-(d.val:ℝ))*paperPairWeight p 1 d.val else 0):ℂ) •
        planePairCreate Q p (rawCreate Q (mode a) 1)) =
      ((1-(d.val:ℝ))*paperPairWeight d.val 1 d.val : ℂ) •
        planePairCreate Q d.val (rawCreate Q (mode a) 1) := by
    rw [Finset.sum_eq_single d.val]
    · simp only [if_true]
    · intro p hp hne
      simp only [Ne.symm hne,if_false,Complex.ofReal_zero,zero_smul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  simp only [planePairHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    planePairRemove_anchored_triple Q _ a b d ha hb,map_add,map_sub,map_smul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [h0,h1,h2]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg,neg_mul,neg_smul,sub_neg_eq_add]


/-- A genuine coefficient creator preserves the literal total orbital level. -/
theorem planePairCreate_single_mem (Q p : ℕ) (d : Fin (Q+1)) :
    planePairCreate Q p (rawCreate Q (mode d) 1) ∈
      threeDegreeSpan Q (p+1+d.val) := by
  classical
  simp only [planePairCreate,coefficientPairCreate,LinearMap.smul_apply,
    LinearMap.sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  by_cases h : i.val+j.val=p+1
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,j,d,by omega,rfl⟩
  · simp only [planePairCoefficient,h,if_false,Complex.ofReal_zero,zero_smul]
    exact Submodule.zero_mem _

/-- The Hamiltonian's true degree preservation follows from its coefficient
deltas and CAR contractions, not a compression used to define H. -/
theorem planePairHamiltonian_threeDegreeSpan (Q D L : ℕ)
    (f : Space Q) (hf : f∈threeDegreeSpan Q L) :
    planePairHamiltonian Q D f ∈ threeDegreeSpan Q L := by
  classical
  have hk : threeDegreeSpan Q L ≤
      Submodule.comap (planePairHamiltonian Q D) (threeDegreeSpan Q L) := by
    apply Submodule.span_le.mpr
    rintro g ⟨a,b,d,hd,rfl⟩
    change planePairHamiltonian Q D
      (rawTripleVector Q (mode a) (mode b) (mode d)) ∈ threeDegreeSpan Q L
    simp only [planePairHamiltonian,LinearMap.sum_apply,Module.End.mul_apply]
    apply Submodule.sum_mem
    intro p hp
    rw [planePairRemove,coefficientPairRemove_tripleVector]
    · simp only [map_add,map_sub,map_smul,Complex.conj_ofReal]
      apply Submodule.add_mem
      · apply Submodule.sub_mem
        · by_cases hab : a.val+b.val=p+1
          · have hdeg : p+1+d.val=L := by omega
            exact Submodule.smul_mem _ _ (hdeg ▸ planePairCreate_single_mem Q p d)
          · simp only [planePairCoefficient,hab,if_false,Complex.ofReal_zero,zero_smul]
            exact Submodule.zero_mem _
        · by_cases had : a.val+d.val=p+1
          · have hdeg : p+1+b.val=L := by omega
            exact Submodule.smul_mem _ _ (hdeg ▸ planePairCreate_single_mem Q p b)
          · simp only [planePairCoefficient,had,if_false,Complex.ofReal_zero,zero_smul]
            exact Submodule.zero_mem _
      · by_cases hbd : b.val+d.val=p+1
        · have hdeg : p+1+a.val=L := by omega
          exact Submodule.smul_mem _ _ (hdeg ▸ planePairCreate_single_mem Q p a)
        · simp only [planePairCoefficient,hbd,if_false,Complex.ofReal_zero,zero_smul]
          exact Submodule.zero_mem _
    · intro i j
      exact_mod_cast planePairCoefficient_antisymm p i.val j.val
  exact hk hf

/-- The literal H-I also preserves the actual three-particle degree block. -/
theorem planeConnected_threeDegreeSpan (Q D L : ℕ)
    (f : Space Q) (hf : f∈threeDegreeSpan Q L) :
    (planePairHamiltonian Q D-1) f ∈ threeDegreeSpan Q L := by
  simp only [LinearMap.sub_apply,Module.End.one_apply]
  exact Submodule.sub_mem _ (planePairHamiltonian_threeDegreeSpan Q D L f hf) hf

end TorusLean.Shared.ThermalCoherentFermionAnchored
