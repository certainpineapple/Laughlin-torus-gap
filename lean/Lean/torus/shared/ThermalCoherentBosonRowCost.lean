import torus.shared.ThermalCoherentBosonRowPhysical
import torus.shared.ThermalCoherentBosonRowEnvelopeCutoff
import torus.shared.ThermalCoherentBosonRowBudget

/-! Every decoded spectator column is injected exactly once into the complete
45-column auxiliary envelope. The original exact Crows square budget then
pays the actual raw Gram correction, without a particle-number bound. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Geometry TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentBosonRowEnvelope TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance rowCost_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Source support and uniqueness, with no dropped or duplicated columns. -/
theorem row_entry_envelope_le (ρ : RowIndex) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ p j, 0≤Q p j) :
    (∑ a : EntryIndex ρ, Q (entryPair ρ a).1 (entryPair ρ a).2) ≤
      ∑ t : Fin 9, ∑ p : Fin (t.val+1), Q p.val (t.val-p.val) := by
  classical
  let I := (t : Fin 9) × Fin (t.val+1)
  let r (a : EntryIndex ρ) : I :=
    ⟨⟨(entryPair ρ a).1+(entryPair ρ a).2,
      Nat.lt_succ_of_le (entry_support ρ a).2.2.2.2.1⟩,
      ⟨(entryPair ρ a).1,by
        change (entryPair ρ a).1 < (entryPair ρ a).1+(entryPair ρ a).2+1
        omega⟩⟩
  have hr : Function.Injective r := by
    intro a b h
    have ht := congrArg (fun z : I => z.1.val) h
    have hp := congrArg (fun z : I => z.2.val) h
    apply entryPair_injective ρ
    apply Prod.ext
    · exact hp
    · change (entryPair ρ a).1+(entryPair ρ a).2=
        (entryPair ρ b).1+(entryPair ρ b).2 at ht
      change (entryPair ρ a).1=(entryPair ρ b).1 at hp
      omega
  let E (x : I) := Q x.2.val (x.1.val-x.2.val)
  have he : (∑ a : EntryIndex ρ, Q (entryPair ρ a).1 (entryPair ρ a).2) =
      ∑ a : EntryIndex ρ, E (r a) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [E,r,Nat.add_sub_cancel_left]
  rw [he]
  rw [←Finset.sum_image (fun a _ b _ hab => hr hab)]
  have hb : (∑ x ∈ Finset.univ.image r, E x) ≤ ∑ x : I, E x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => hQ _ _)
  simpa only [I,Fintype.sum_sigma,E] using hb

/-- All row auxiliaries are true a_j B_p outputs in the common envelope. -/
theorem actualRowAuxiliary_envelope_le (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ a : EntryIndex ρ, q (actualRowAuxiliary G theta ρ a R f)) ≤
      auxiliaryEnvelope G theta 8 f R := by
  have h := row_entry_envelope_le ρ
    (fun p j => q (singleJetAnnihilator G theta j R (pairDescendant G theta p R f)))
    (fun _ _ => occupationMetricNormSq_nonneg _ _)
  rw [Fin.sum_univ_eq_sum_range (fun t => ∑ p : Fin (t+1),
    q (singleJetAnnihilator G theta (t-p.val) R (pairDescendant G theta p.val R f))) 9] at h
  exact h

/-- The original 138-row Gram error has the exact source Crows budget. -/
theorem actualRows_metric_pointwise (G : Geometry) (theta : Twist) (R : ℂ)
    (hG : 20≤systole G) (f : Core (OrbitalIndex G theta) ℂ) :
    ‖∑ ρ : RowIndex, actualRowMetricCross G theta ρ R f f‖ ≤
      allowance*rowCost*auxiliaryEnvelope G theta 8 f R := by
  have he : 0≤allowance := by norm_num [allowance]
  calc
    _ ≤ ∑ ρ : RowIndex, ‖actualRowMetricCross G theta ρ R f f‖ := norm_sum_le _ _
    _ ≤ ∑ ρ : RowIndex, allowance*((∑ a : EntryIndex ρ, (rowAlpha ρ a)^2)*
          auxiliaryEnvelope G theta 8 f R) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      apply (actualRowMetric_bound G theta ρ R hG f).trans
      apply mul_le_mul_of_nonneg_left _ he
      apply (actualRowGrouped_bound G theta ρ R f).trans
      exact mul_le_mul_of_nonneg_left (actualRowAuxiliary_envelope_le G theta ρ R f)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by
      simp only [←mul_assoc]
      rw [←Finset.sum_mul,←Finset.mul_sum,Crows_exact]
      rfl

end TorusLean.Shared.ThermalCoherentBosonRows
