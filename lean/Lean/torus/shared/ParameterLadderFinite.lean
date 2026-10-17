import torus.shared.ParameterLadderIntegration

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterLadderIntegration MeasureTheory
open scoped ComplexConjugate BigOperators

/-- Only levels actually used by a finite COM certificate are required. -/
structure IsFiniteLadderFamily (G : Geometry) (theta : Twist) (k H : ℕ)
    (w : ℕ → ℂ → ℂ) : Prop where
  smooth : ∀ n, n ≤ H → ContDiff ℝ 1 (w n)
  boundary : ∀ n, n ≤ H → HasDualBoundary G theta k (w n)
  raise_eq : ∀ n, n < H → parameterRaise k (w n) = w (n+1)
  lower_zero : parameterLower k (w 0) = 0
  lower_succ : ∀ n, n < H → parameterLower k (w (n+1)) = ((n+1:ℕ):ℂ) • w n

theorem vacuum_descendant_inner_zero_finite (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (H : ℕ) (w z : ℕ → ℂ → ℂ) (hw : IsFiniteLadderFamily G theta k H w)
    (hz : IsFiniteLadderFamily G theta k H z) (m : ℕ) (hm : m+1 ≤ H) :
    cellInner G k (w 0) (z (m+1)) = 0 := by
  rw [← hz.raise_eq m (by omega), ← parameterLower_adjoint G theta k (w 0) (z m)
    (hw.smooth 0 (by omega)) (hz.smooth m (by omega)) (hw.boundary 0 (by omega)) (hz.boundary m (by omega)), hw.lower_zero]
  simp [cellInner]

/-- True charge-k cell orthogonality of distinct COM levels, retaining the
full relative matrix unit between the two possibly nonorthogonal vacua. -/
theorem ladder_cellInner_finite (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (H : ℕ) (w z : ℕ → ℂ → ℂ) (hw : IsFiniteLadderFamily G theta k H w)
    (hz : IsFiniteLadderFamily G theta k H z) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    cellInner G k (w n) (z m) =
      if n = m then (n.factorial : ℂ) * cellInner G k (w 0) (z 0) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m => simpa using vacuum_descendant_inner_zero_finite G theta k H w z hw hz m hm
  | succ n ih =>
    cases m with
    | zero =>
      have h := vacuum_descendant_inner_zero_finite G theta k H z w hz hw n hn
      have hh := congrArg (fun a : ℂ => conj a) h
      simpa only [cellInner_conj_symm, map_zero, Nat.succ_ne_zero, ite_false] using hh
    | succ m =>
      rw [← hz.raise_eq m (by omega), ← parameterLower_adjoint G theta k (w (n+1)) (z m)
        (hw.smooth _ (by omega)) (hz.smooth _ (by omega)) (hw.boundary _ (by omega)) (hz.boundary _ (by omega)),
        hw.lower_succ n (by omega), cellInner_smul_left, ih m (by omega) (by omega)]
      simp only [map_natCast, Nat.succ.injEq]
      by_cases h : n = m
      · subst m
        simp only [ite_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      · simp [h]


theorem normalized_ladder_cellInner_finite (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (H : ℕ) (w z : ℕ → ℂ → ℂ) (hw : IsFiniteLadderFamily G theta k H w)
    (hz : IsFiniteLadderFamily G theta k H z) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    cellInner G k (normalizedLevel w n) (normalizedLevel z m) =
      if n = m then cellInner G k (w 0) (z 0) else 0 := by
  rw [normalizedLevel, normalizedLevel, cellInner_smul_left, cellInner_smul_right,
    ladder_cellInner_finite G theta k H w z hw hz n m hn hm]
  simp only [map_inv₀, Complex.conj_ofReal]
  by_cases h : n = m
  · subst m
    simp only [ite_true]
    have hs : (Real.sqrt (n.factorial : ℝ) : ℂ)^2 = (n.factorial : ℂ) := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)
    have hn : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    rw [← hs]
    field_simp
  · simp [h]


theorem normalized_ladder_mu2_finite (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (H : ℕ) (w z : ℕ → ℂ → ℂ) (hw : IsFiniteLadderFamily G theta k H w)
    (hz : IsFiniteLadderFamily G theta k H z) (n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    cellInner G 2 (normalizedLevel w n) (normalizedLevel z m) =
      if n = m then ((2/(k:ℝ) : ℝ) : ℂ) * cellInner G k (w 0) (z 0) else 0 := by
  change (∫ R, conj (normalizedLevel w n R) * normalizedLevel z m R ∂cellMeasure G 2) = _
  rw [cellIntegral_two_eq_charge G k]
  change ((2/(k:ℝ) : ℝ) : ℂ) * cellInner G k (normalizedLevel w n) (normalizedLevel z m) = _
  rw [normalized_ladder_cellInner_finite G theta k H w z hw hz n m hn hm]
  split_ifs <;> simp

/-- Finite COM partial-trace algebra after the genuine cell adjoint/ladder
identities. Relative labels are not made orthogonal or scalarized. -/
theorem finite_ladder_partial_trace_bounded {A B : Type*} [Fintype A] [Fintype B]
    (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] (H : ℕ)
    (w : A → ℕ → ℂ → ℂ) (z : B → ℕ → ℂ → ℂ)
    (hw : ∀ a, IsFiniteLadderFamily G theta k H (w a))
    (hz : ∀ b, IsFiniteLadderFamily G theta k H (z b))
    (C : (A × Fin (H+1)) → (B × Fin (H+1)) → ℂ) :
    (∫ R, ∑ u : A × Fin (H+1), ∑ v : B × Fin (H+1),
      C u v * (conj (normalizedLevel (w u.1) u.2 R) * normalizedLevel (z v.1) v.2 R)
      ∂cellMeasure G 2) =
    ((2/(k:ℝ) : ℝ) : ℂ) * ∑ u : A × Fin (H+1), ∑ b : B,
      C u (b,u.2) * cellInner G k (w u.1 0) (z b 0) := by
  classical
  have hi (u : A × Fin (H+1)) (v : B × Fin (H+1)) : Integrable (fun R =>
      C u v * (conj (normalizedLevel (w u.1) u.2 R) * normalizedLevel (z v.1) v.2 R))
      (cellMeasure G 2) := by
    apply continuous_integrable_cellMeasure
    apply Continuous.const_mul
    apply Continuous.mul
    · exact Complex.continuous_conj.comp (((hw u.1).smooth u.2 (Nat.le_of_lt_succ u.2.isLt)).continuous.const_smul _)
    · exact ((hz v.1).smooth v.2 (Nat.le_of_lt_succ v.2.isLt)).continuous.const_smul _
  rw [integral_finsetSum Finset.univ (fun u _ => integrable_finsetSum Finset.univ (fun v _ => hi u v))]
  simp_rw [integral_finsetSum Finset.univ (fun v _ => hi _ v), integral_const_mul]
  change (∑ u : A × Fin (H+1), ∑ v : B × Fin (H+1),
    C u v * cellInner G 2 (normalizedLevel (w u.1) u.2) (normalizedLevel (z v.1) v.2)) = _
  simp_rw [normalized_ladder_mu2_finite G theta k H _ _ (hw _) (hz _) _ _ (Nat.le_of_lt_succ (Fin.isLt _)) (Nat.le_of_lt_succ (Fin.isLt _))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_ite, mul_zero, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring


#print axioms finite_ladder_partial_trace_bounded
end TorusLean.Shared.ParameterLadderFinite
