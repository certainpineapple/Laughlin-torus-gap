import torus.shared.BosonFiniteCertificateNatCOMRaiseCompatibility
import torus.shared.BosonFiniteCertificateThreeOccupationComplete

/-! All stored finite D matrices are initial descendants of the genuine
unbounded-label Nat raising derivation. Only endpoints through degree eight
are asserted; the operator on the left has no truncation at any degree. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem c300desc0_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify c300desc0 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c300desc0_root]

#print axioms c300desc0_actual_Nat

theorem c300desc1_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify c300desc1 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc0_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 0 k300occ k300_particle_degree k300_orbital_degree
    (complexify c300desc0 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 0 (by decide) _ hh.1 hh.2,
    k300_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise0 * c300desc0 = c300desc1 from c300desc1_step]

#print axioms c300desc1_actual_Nat

theorem c300desc2_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify c300desc2 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc1_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree
    (complexify c300desc1 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 1 (by decide) _ hh.1 hh.2,
    k301_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise1 * c300desc1 = c300desc2 from c300desc2_step]

#print axioms c300desc2_actual_Nat

theorem c300desc3_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify c300desc3 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc2_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 2 k302occ k302_particle_degree k302_orbital_degree
    (complexify c300desc2 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 2 (by decide) _ hh.1 hh.2,
    k302_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise2 * c300desc2 = c300desc3 from c300desc3_step]

#print axioms c300desc3_actual_Nat

theorem c300desc4_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify c300desc4 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc3_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree
    (complexify c300desc3 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 3 (by decide) _ hh.1 hh.2,
    k303_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise3 * c300desc3 = c300desc4 from c300desc4_step]

#print axioms c300desc4_actual_Nat

theorem c300desc5_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c300desc5 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc4_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree
    (complexify c300desc4 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 4 (by decide) _ hh.1 hh.2,
    k304_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise4 * c300desc4 = c300desc5 from c300desc5_step]

#print axioms c300desc5_actual_Nat

theorem c300desc6_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c300desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c300desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c300desc5 = c300desc6 from c300desc6_step]

#print axioms c300desc6_actual_Nat

theorem c300desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c300desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c300desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c300desc6 = c300desc7 from c300desc7_step]

#print axioms c300desc7_actual_Nat

theorem c300desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c300desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c300desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c300desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c300desc7 = c300desc8 from c300desc8_step]

#print axioms c300desc8_actual_Nat

theorem c301desc1_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify c301desc1 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c301desc1_root]

#print axioms c301desc1_actual_Nat

theorem c301desc2_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify c301desc2 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc1_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree
    (complexify c301desc1 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 1 (by decide) _ hh.1 hh.2,
    k301_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise1 * c301desc1 = c301desc2 from c301desc2_step]

#print axioms c301desc2_actual_Nat

theorem c301desc3_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify c301desc3 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc2_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 2 k302occ k302_particle_degree k302_orbital_degree
    (complexify c301desc2 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 2 (by decide) _ hh.1 hh.2,
    k302_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise2 * c301desc2 = c301desc3 from c301desc3_step]

#print axioms c301desc3_actual_Nat

theorem c301desc4_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify c301desc4 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc3_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree
    (complexify c301desc3 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 3 (by decide) _ hh.1 hh.2,
    k303_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise3 * c301desc3 = c301desc4 from c301desc4_step]

#print axioms c301desc4_actual_Nat

theorem c301desc5_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c301desc5 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc4_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree
    (complexify c301desc4 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 4 (by decide) _ hh.1 hh.2,
    k304_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise4 * c301desc4 = c301desc5 from c301desc5_step]

#print axioms c301desc5_actual_Nat

theorem c301desc6_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c301desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c301desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c301desc5 = c301desc6 from c301desc6_step]

#print axioms c301desc6_actual_Nat

theorem c301desc7_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c301desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c301desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c301desc6 = c301desc7 from c301desc7_step]

#print axioms c301desc7_actual_Nat

theorem c301desc8_actual_Nat (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c301desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c301desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c301desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c301desc7 = c301desc8 from c301desc8_step]

#print axioms c301desc8_actual_Nat

theorem c302desc2_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify c302desc2 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c302desc2_root]

#print axioms c302desc2_actual_Nat

theorem c302desc3_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify c302desc3 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc2_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 2 k302occ k302_particle_degree k302_orbital_degree
    (complexify c302desc2 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 2 (by decide) _ hh.1 hh.2,
    k302_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise2 * c302desc2 = c302desc3 from c302desc3_step]

#print axioms c302desc3_actual_Nat

theorem c302desc4_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify c302desc4 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc3_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree
    (complexify c302desc3 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 3 (by decide) _ hh.1 hh.2,
    k303_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise3 * c302desc3 = c302desc4 from c302desc4_step]

#print axioms c302desc4_actual_Nat

theorem c302desc5_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c302desc5 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc4_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree
    (complexify c302desc4 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 4 (by decide) _ hh.1 hh.2,
    k304_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise4 * c302desc4 = c302desc5 from c302desc5_step]

#print axioms c302desc5_actual_Nat

theorem c302desc6_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c302desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c302desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c302desc5 = c302desc6 from c302desc6_step]

#print axioms c302desc6_actual_Nat

theorem c302desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c302desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c302desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c302desc6 = c302desc7 from c302desc7_step]

#print axioms c302desc7_actual_Nat

theorem c302desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c302desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c302desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c302desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c302desc7 = c302desc8 from c302desc8_step]

#print axioms c302desc8_actual_Nat

theorem c303desc3_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify c303desc3 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c303desc3_root]

#print axioms c303desc3_actual_Nat

theorem c303desc4_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify c303desc4 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c303desc3_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree
    (complexify c303desc3 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 3 (by decide) _ hh.1 hh.2,
    k303_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise3 * c303desc3 = c303desc4 from c303desc4_step]

#print axioms c303desc4_actual_Nat

theorem c303desc5_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c303desc5 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c303desc4_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree
    (complexify c303desc4 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 4 (by decide) _ hh.1 hh.2,
    k304_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise4 * c303desc4 = c303desc5 from c303desc5_step]

#print axioms c303desc5_actual_Nat

theorem c303desc6_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c303desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c303desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c303desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c303desc5 = c303desc6 from c303desc6_step]

#print axioms c303desc6_actual_Nat

theorem c303desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c303desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c303desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c303desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c303desc6 = c303desc7 from c303desc7_step]

#print axioms c303desc7_actual_Nat

theorem c303desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c303desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c303desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c303desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c303desc7 = c303desc8 from c303desc8_step]

#print axioms c303desc8_actual_Nat

theorem c304desc4_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify c304desc4 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c304desc4_root]

#print axioms c304desc4_actual_Nat

theorem c304desc5_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c304desc5 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c304desc4_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree
    (complexify c304desc4 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 4 (by decide) _ hh.1 hh.2,
    k304_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise4 * c304desc4 = c304desc5 from c304desc5_step]

#print axioms c304desc5_actual_Nat

theorem c304desc6_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c304desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c304desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c304desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c304desc5 = c304desc6 from c304desc6_step]

#print axioms c304desc6_actual_Nat

theorem c304desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c304desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c304desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c304desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c304desc6 = c304desc7 from c304desc7_step]

#print axioms c304desc7_actual_Nat

theorem c304desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c304desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c304desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c304desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c304desc7 = c304desc8 from c304desc8_step]

#print axioms c304desc8_actual_Nat

theorem c305desc5_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify c305desc5 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c305desc5_root]

#print axioms c305desc5_actual_Nat

theorem c305desc6_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c305desc6 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c305desc5_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree
    (complexify c305desc5 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 5 (by decide) _ hh.1 hh.2,
    k305_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise5 * c305desc5 = c305desc6 from c305desc6_step]

#print axioms c305desc6_actual_Nat

theorem c305desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c305desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c305desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c305desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c305desc6 = c305desc7 from c305desc7_step]

#print axioms c305desc7_actual_Nat

theorem c305desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c305desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c305desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c305desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c305desc7 = c305desc8 from c305desc8_step]

#print axioms c305desc8_actual_Nat

theorem c306desc6_actual_Nat (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify c306desc6 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c306desc6_root]

#print axioms c306desc6_actual_Nat

theorem c306desc7_actual_Nat (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c306desc7 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c306desc6_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree
    (complexify c306desc6 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 6 (by decide) _ hh.1 hh.2,
    k306_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise6 * c306desc6 = c306desc7 from c306desc7_step]

#print axioms c306desc7_actual_Nat

theorem c306desc8_actual_Nat (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c306desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c306desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c306desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c306desc7 = c306desc8 from c306desc8_step]

#print axioms c306desc8_actual_Nat

theorem c307desc7_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify b307relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify c307desc7 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c307desc7_root]

#print axioms c307desc7_actual_Nat

theorem c307desc8_actual_Nat (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify b307relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c307desc8 *ᵥ x)) := by
  rw [Function.iterate_succ_apply',c307desc7_actual_Nat]
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree
    (complexify c307desc7 *ᵥ x)
  rw [canonicalCOMRaiseNat_rename_homogeneous_three 7 (by decide) _ hh.1 hh.2,
    k307_actual_raise_block,Matrix.mulVec_mulVec,← complexify_mul_rect,
    show c300raise7 * c307desc7 = c307desc8 from c307desc8_step]

#print axioms c307desc8_actual_Nat

theorem c308desc8_actual_Nat (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify b308relative *ᵥ x))) =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify c308desc8 *ᵥ x)) := by
  rw [Function.iterate_zero_apply,c308desc8_root]

#print axioms c308desc8_actual_Nat
end TorusLean.BosonFiniteCertificate
