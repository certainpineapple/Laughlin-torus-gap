import TwoBodyLift

/-! True CCR normal ordering on the original finite bosonic polynomial core.
This algebraic layer keeps every raw-mode overlap and the zero-contraction
four-body order. Literal frozen-row decoding and identification with the
separately constructed three- and four-body sources are subsequent interfaces.
No particle-number estimate or orthogonality of the raw modes is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowCCR
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Actual two-creation cross form after the one true CCR contraction. -/
theorem modeCreate_cross_normal_order (u v : Orbital ι) (x y : Core ι ℂ) :
    ip (modeCreate u x) (modeCreate v y) =
      ip (modeAnnihilate v x) (modeAnnihilate u y) + (inner ℂ u v)*ip x y := by
  change occupationInner (fun _ : ι => 1) (modeCreate u x) (modeCreate v y) = _
  rw [mode_create_adjoint,mode_mixed_ccr]
  simp only [ip,occupationInner_add_right,occupationInner_smul_right]
  exact congrArg (fun z => z + (inner ℂ u v)*ip x y)
    (mode_annihilate_adjoint v x (modeAnnihilate u y)).symm

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Original grouped row: its pair component plus actual creators on outputs. -/
def rowApply (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f : Core ι ℂ) : Core ι ℂ :=
  P f + ∑ i, modeCreate (u i) (Y i f)

/-- Cross terms with the pair row and the identity part of the single contraction. -/
def rowThreeCross (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f g : Core ι ℂ) : ℂ :=
  (∑ i, ip (modeAnnihilate (u i) (P f)) (Y i g)) +
  (∑ i, ip (Y i f) (modeAnnihilate (u i) (P g))) + ∑ i, ip (Y i f) (Y i g)

/-- The exact zero-contraction word: the left and right auxiliary modes cross. -/
def rowFourCross (u : I → Orbital ι)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f g : Core ι ℂ) : ℂ :=
  ∑ i, ∑ j, ip (modeAnnihilate (u j) (Y i f)) (modeAnnihilate (u i) (Y j g))

/-- The only raw-jet correction to the canonical normal ordering. -/
def rowMetricCross (u : I → Orbital ι)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f g : Core ι ℂ) : ℂ :=
  ∑ i, ∑ j, (inner ℂ (u i) (u j) - if i=j then 1 else 0) * ip (Y i f) (Y j g)

/-- Uncollected entries give this same row without any multiplicity factor. -/
theorem rowApply_grouped {J : Type*} [Fintype J]
    (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (r : J → I) (c : J → ℂ) (X : J → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f : Core ι ℂ) :
    rowApply u P (fun i => ∑ a ∈ Finset.univ.filter (fun a => r a=i), c a • X a) f =
      P f + ∑ a, c a • modeCreate (u (r a)) (X a f) := by
  classical
  unfold rowApply
  apply congrArg (fun z => P f + z)
  calc
    _ = ∑ i, ∑ a ∈ Finset.univ.filter (fun a => r a=i),
        c a • modeCreate (u i) (X a f) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply,map_sum,map_smul]
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_ite_eq_of_mem Finset.univ (r a)
        (fun i => c a • modeCreate (u i) (X a f)) (Finset.mem_univ _)

/-- The actual all-Core complex identity, before restricting a particle sector. -/
theorem rowApply_cross_normal_order
    (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f g : Core ι ℂ) :
    ip (rowApply u P Y f) (rowApply u P Y g) =
      ip (P f) (P g) + rowThreeCross u P Y f g +
        rowFourCross u Y f g + rowMetricCross u Y f g := by
  have hm : (∑ i, ∑ j, (inner ℂ (u i) (u j))*ip (Y i f) (Y j g)) =
      (∑ i, ip (Y i f) (Y i g)) + rowMetricCross u Y f g := by
    unfold rowMetricCross
    simp only [sub_mul,Finset.sum_sub_distrib]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  have hcc : (∑ i, ∑ j, ip (modeCreate (u i) (Y i f)) (modeCreate (u j) (Y j g))) =
      rowFourCross u Y f g + ∑ i, ∑ j, (inner ℂ (u i) (u j))*ip (Y i f) (Y j g) := by
    simp only [modeCreate_cross_normal_order,Finset.sum_add_distrib,rowFourCross]
  have hl : (∑ i, ip (P f) (modeCreate (u i) (Y i g))) =
      ∑ i, ip (modeAnnihilate (u i) (P f)) (Y i g) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (mode_annihilate_adjoint (u i) (P f) (Y i g)).symm
  have hr : (∑ i, ip (modeCreate (u i) (Y i f)) (P g)) =
      ∑ i, ip (Y i f) (modeAnnihilate (u i) (P g)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mode_create_adjoint (u i) (Y i f) (P g)
  have he : ip (rowApply u P Y f) (rowApply u P Y g) =
      ip (P f) (P g) + (∑ i, ip (P f) (modeCreate (u i) (Y i g))) +
      (∑ i, ip (modeCreate (u i) (Y i f)) (P g)) +
      ∑ i, ∑ j, ip (modeCreate (u i) (Y i f)) (modeCreate (u j) (Y j g)) := by
    simp only [rowApply,ip,occupationInner_add_left,occupationInner_add_right,
      inner_sum_left,inner_sum_right]
    have hs : (∑ j, ∑ i, occupationInner (fun _ : ι => 1)
        (modeCreate (u i) (Y i f)) (modeCreate (u j) (Y j g))) =
        ∑ i, ∑ j, occupationInner (fun _ : ι => 1)
          (modeCreate (u i) (Y i f)) (modeCreate (u j) (Y j g)) := Finset.sum_comm
    rw [hs]
    ring
  rw [he,hl,hr]
  rw [hcc,hm]
  unfold rowThreeCross
  ring

/-- Diagonal specialization is a true norm square and is nonnegative. -/
theorem rowApply_normSq_nonneg
    (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f : Core ι ℂ) :
    0 ≤ q (rowApply u P Y f) := occupationMetricNormSq_nonneg _ _

theorem rowApply_normSq_normal_order
    (u : I → Orbital ι) (P : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (Y : I → Core ι ℂ →ₗ[ℂ] Core ι ℂ) (f : Core ι ℂ) :
    q (rowApply u P Y f) = q (P f) + (rowThreeCross u P Y f f).re +
      (rowFourCross u Y f f).re + (rowMetricCross u Y f f).re := by
  have h := congrArg Complex.re (rowApply_cross_normal_order u P Y f f)
  simpa only [Complex.add_re,occupationInner_self_re] using h

end TorusLean.Shared.ThermalCoherentBosonRowCCR
