import torus.shared.BosonFiniteCertificateNatCOMCompatibility
import torus.shared.BosonFiniteCertificateThreeOccupationNat

/-! Original relative families as true vacua of unbounded-label COM lowering.
The kernel statements quantify over all Nat-orbital homogeneous N=3
polynomials at degrees 0,...,8; the earlier carrier exhaustiveness and actual
lowering intertwining are both used. Arbitrarily high descendants are formed
with the actual Nat raising derivation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem k300_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k300_actual_relative_vacuum,map_zero]

theorem k300_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))).IsWeightedHomogeneous id 0 := by
  exact rename_canonicalBlock_bihomogeneous 0 k300occ
    k300_particle_degree k300_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k300_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 0) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k300_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k300_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k300_nat_relative_vacuum]

theorem k300_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 0 n _
    (k300_nat_relative_bihomogeneous x).1 (k300_nat_relative_bihomogeneous x).2
    (k300_nat_relative_vacuum x)

theorem k301_nat_relative_vacuum (x : Fin 0 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k301_actual_relative_vacuum,map_zero]

theorem k301_nat_relative_bihomogeneous (x : Fin 0 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))).IsWeightedHomogeneous id 1 := by
  exact rename_canonicalBlock_bihomogeneous 1 k301occ
    k301_particle_degree k301_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k301_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 1) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 0 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k301_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k301_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k301_nat_relative_vacuum]

theorem k301_nat_relative_descendant_lower (x : Fin 0 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 1 n _
    (k301_nat_relative_bihomogeneous x).1 (k301_nat_relative_bihomogeneous x).2
    (k301_nat_relative_vacuum x)

theorem k302_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k302_actual_relative_vacuum,map_zero]

theorem k302_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x))).IsWeightedHomogeneous id 2 := by
  exact rename_canonicalBlock_bihomogeneous 2 k302occ
    k302_particle_degree k302_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k302_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 2) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k302_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k302_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k302_nat_relative_vacuum]

theorem k302_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 2 n _
    (k302_nat_relative_bihomogeneous x).1 (k302_nat_relative_bihomogeneous x).2
    (k302_nat_relative_vacuum x)

theorem k303_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k303_actual_relative_vacuum,map_zero]

theorem k303_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))).IsWeightedHomogeneous id 3 := by
  exact rename_canonicalBlock_bihomogeneous 3 k303occ
    k303_particle_degree k303_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k303_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 3) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k303_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k303_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k303_nat_relative_vacuum]

theorem k303_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 3 n _
    (k303_nat_relative_bihomogeneous x).1 (k303_nat_relative_bihomogeneous x).2
    (k303_nat_relative_vacuum x)

theorem k304_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k304_actual_relative_vacuum,map_zero]

theorem k304_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x))).IsWeightedHomogeneous id 4 := by
  exact rename_canonicalBlock_bihomogeneous 4 k304occ
    k304_particle_degree k304_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k304_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 4) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k304_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k304_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k304_nat_relative_vacuum]

theorem k304_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 4 n _
    (k304_nat_relative_bihomogeneous x).1 (k304_nat_relative_bihomogeneous x).2
    (k304_nat_relative_vacuum x)

theorem k305_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k305_actual_relative_vacuum,map_zero]

theorem k305_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))).IsWeightedHomogeneous id 5 := by
  exact rename_canonicalBlock_bihomogeneous 5 k305occ
    k305_particle_degree k305_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k305_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 5) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k305_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k305_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k305_nat_relative_vacuum]

theorem k305_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 5 n _
    (k305_nat_relative_bihomogeneous x).1 (k305_nat_relative_bihomogeneous x).2
    (k305_nat_relative_vacuum x)

theorem k306_nat_relative_vacuum (x : Fin 2 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k306_actual_relative_vacuum,map_zero]

theorem k306_nat_relative_bihomogeneous (x : Fin 2 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))).IsWeightedHomogeneous id 6 := by
  exact rename_canonicalBlock_bihomogeneous 6 k306occ
    k306_particle_degree k306_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k306_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 6) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 2 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k306_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k306_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k306_nat_relative_vacuum]

theorem k306_nat_relative_descendant_lower (x : Fin 2 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 6 n _
    (k306_nat_relative_bihomogeneous x).1 (k306_nat_relative_bihomogeneous x).2
    (k306_nat_relative_vacuum x)

theorem k307_nat_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k307_actual_relative_vacuum,map_zero]

theorem k307_nat_relative_bihomogeneous (x : Fin 1 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))).IsWeightedHomogeneous id 7 := by
  exact rename_canonicalBlock_bihomogeneous 7 k307occ
    k307_particle_degree k307_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k307_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 7) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 1 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k307_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k307_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k307_nat_relative_vacuum]

theorem k307_nat_relative_descendant_lower (x : Fin 1 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 7 n _
    (k307_nat_relative_bihomogeneous x).1 (k307_nat_relative_bihomogeneous x).2
    (k307_nat_relative_vacuum x)

theorem k308_nat_relative_vacuum (x : Fin 2 → ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) = 0 := by
  rw [canonicalCOMLowerNat_rename,k308_actual_relative_vacuum,map_zero]

theorem k308_nat_relative_bihomogeneous (x : Fin 2 → ℂ) :
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))).IsHomogeneous 3 ∧
    (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))).IsWeightedHomogeneous id 8 := by
  exact rename_canonicalBlock_bihomogeneous 8 k308occ
    k308_particle_degree k308_orbital_degree _

/-- Full actual Nat-lowering kernel, with no preselected-span hypothesis. -/
theorem k308_nat_homogeneous_relative_kernel (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 8) :
    canonicalCOMLowerNat f=0 ↔ ∃ x : Fin 2 → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)) = f := by
  obtain ⟨v,rfl⟩ := k308_nat_homogeneous_block f hN hd
  constructor
  · intro h
    have hl := (canonicalCOMLowerNat_rename_eq_zero_iff _).mp h
    obtain ⟨x,hx⟩ := (k308_actual_relative_kernel v).mp hl
    exact ⟨x,congrArg (MvPolynomial.rename Fin.val) hx⟩
  · rintro ⟨x,hx⟩
    rw [← hx,k308_nat_relative_vacuum]

theorem k308_nat_relative_descendant_lower (x : Fin 2 → ℂ) (n : ℕ) :
    canonicalCOMLowerNat
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)))) =
    (3*((n:ℂ)+1)) •
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)))) := by
  exact canonicalCOMNat_lower_iterate 8 n _
    (k308_nat_relative_bihomogeneous x).1 (k308_nat_relative_bihomogeneous x).2
    (k308_nat_relative_vacuum x)
#print axioms k300_nat_relative_vacuum
#print axioms k300_nat_relative_bihomogeneous
#print axioms k300_nat_homogeneous_relative_kernel
#print axioms k300_nat_relative_descendant_lower
#print axioms k301_nat_relative_vacuum
#print axioms k301_nat_relative_bihomogeneous
#print axioms k301_nat_homogeneous_relative_kernel
#print axioms k301_nat_relative_descendant_lower
#print axioms k302_nat_relative_vacuum
#print axioms k302_nat_relative_bihomogeneous
#print axioms k302_nat_homogeneous_relative_kernel
#print axioms k302_nat_relative_descendant_lower
#print axioms k303_nat_relative_vacuum
#print axioms k303_nat_relative_bihomogeneous
#print axioms k303_nat_homogeneous_relative_kernel
#print axioms k303_nat_relative_descendant_lower
#print axioms k304_nat_relative_vacuum
#print axioms k304_nat_relative_bihomogeneous
#print axioms k304_nat_homogeneous_relative_kernel
#print axioms k304_nat_relative_descendant_lower
#print axioms k305_nat_relative_vacuum
#print axioms k305_nat_relative_bihomogeneous
#print axioms k305_nat_homogeneous_relative_kernel
#print axioms k305_nat_relative_descendant_lower
#print axioms k306_nat_relative_vacuum
#print axioms k306_nat_relative_bihomogeneous
#print axioms k306_nat_homogeneous_relative_kernel
#print axioms k306_nat_relative_descendant_lower
#print axioms k307_nat_relative_vacuum
#print axioms k307_nat_relative_bihomogeneous
#print axioms k307_nat_homogeneous_relative_kernel
#print axioms k307_nat_relative_descendant_lower
#print axioms k308_nat_relative_vacuum
#print axioms k308_nat_relative_bihomogeneous
#print axioms k308_nat_homogeneous_relative_kernel
#print axioms k308_nat_relative_descendant_lower
end TorusLean.BosonFiniteCertificate
