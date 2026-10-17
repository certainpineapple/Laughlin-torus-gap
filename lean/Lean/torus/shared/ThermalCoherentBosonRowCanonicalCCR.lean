import torus.shared.ThermalCoherentBosonRowCanonicalAuxiliary

/-! The original nine creation labels, acting on the existing finite-support
Nat polynomial core. Only finite sums and the already established occupation
adjoints enter; no completion or new infinite-dimensional CCR is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators

private theorem nat_create_cross (i j : Fin 9) (f g : Core ℕ ℂ) :
    natOccupationInner (create i.val f) (create j.val g) =
      natOccupationInner (annihilate j.val f) (annihilate i.val g) +
        if i=j then natOccupationInner f g else 0 := by
  rw [nat_create_adjoint,annihilate_create,natOccupationInner_add_right,
    ←nat_annihilate_adjoint]
  by_cases h : i=j
  · subst j
    simp only [ite_true]
  · have hv : i.val≠j.val := fun he => h (Fin.ext he)
    simp only [h,hv,ite_false,natOccupationInner_zero_right]

def canonicalRowPair (ρ : RowIndex) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (rowLambda ρ:ℂ) • (natPairNormalization ρ.1.val • canonicalPairNat ρ.1.val)

def canonicalRowGrouped (ρ : RowIndex) (i : Fin 9) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a => entryJet ρ a=i.val),
    (rowAlpha ρ a:ℂ) • canonicalPairSpectator (entryPair ρ a).1 (entryPair ρ a).2

/-- The actual source row is grouped by its original created orbital label. -/
theorem canonicalNatRow_grouped (ρ : RowIndex) (f : Core ℕ ℂ) :
    canonicalNatRow ρ.1.val (rowData ρ) f = canonicalRowPair ρ f +
      ∑ i : Fin 9, create i.val (canonicalRowGrouped ρ i f) := by
  rw [canonicalNatRow_decoded,LinearMap.add_apply,LinearMap.sum_apply]
  change canonicalRowPair ρ f + _ = _
  congr 1
  simp only [canonicalRowGrouped,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  let i : Fin 9 := ⟨entryJet ρ a,Nat.lt_succ_of_le (entry_support ρ a).2.2.2.2.2⟩
  have he (j : Fin 9) : entryJet ρ a=j.val ↔ j=i := by
    constructor
    · intro h; exact Fin.ext h.symm
    · intro h; subst j; rfl
  rw [Finset.sum_eq_single i]
  · simp only [he,ite_true,LinearMap.smul_apply,LinearMap.comp_apply,map_smul,
      canonicalPairSpectator,i]
  · intro b _ hb
    simp only [he,hb,ite_false,LinearMap.zero_apply,map_zero]
  · simp

/-- Genuine finite canonical normal ordering. The metric is exactly the
Kronecker metric here; the physical raw-jet correction is a separate theorem. -/
theorem canonicalNatRow_cross_normal_order (ρ : RowIndex) (f g : Core ℕ ℂ) :
    natOccupationInner (canonicalNatRow ρ.1.val (rowData ρ) f)
      (canonicalNatRow ρ.1.val (rowData ρ) g) =
      natOccupationInner (canonicalRowPair ρ f) (canonicalRowPair ρ g) +
      (∑ i : Fin 9, natOccupationInner (annihilate i.val (canonicalRowPair ρ f))
        (canonicalRowGrouped ρ i g)) +
      (∑ i : Fin 9, natOccupationInner (canonicalRowGrouped ρ i f)
        (annihilate i.val (canonicalRowPair ρ g))) +
      (∑ i : Fin 9, natOccupationInner (canonicalRowGrouped ρ i f)
        (canonicalRowGrouped ρ i g)) +
      ∑ i : Fin 9, ∑ j : Fin 9,
        natOccupationInner (annihilate j.val (canonicalRowGrouped ρ i f))
          (annihilate i.val (canonicalRowGrouped ρ j g)) := by
  rw [canonicalNatRow_grouped,canonicalNatRow_grouped]
  simp only [natOccupationInner_add_left,natOccupationInner_add_right,
    natOccupationInner_sum_left,natOccupationInner_sum_right]
  have hl (i : Fin 9) := nat_annihilate_adjoint i.val (canonicalRowPair ρ f)
    (canonicalRowGrouped ρ i g)
  simp_rw [nat_create_cross,←hl,nat_create_adjoint]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hswap : (∑ i : Fin 9, ∑ j : Fin 9,
      natOccupationInner (annihilate i.val (canonicalRowGrouped ρ j f))
        (annihilate j.val (canonicalRowGrouped ρ i g))) =
      ∑ i : Fin 9, ∑ j : Fin 9,
        natOccupationInner (annihilate j.val (canonicalRowGrouped ρ i f))
          (annihilate i.val (canonicalRowGrouped ρ j g)) := Finset.sum_comm
  rw [hswap]
  ring

#print axioms canonicalNatRow_grouped
#print axioms canonicalNatRow_cross_normal_order
end TorusLean.Shared.ThermalCoherentBosonRows
