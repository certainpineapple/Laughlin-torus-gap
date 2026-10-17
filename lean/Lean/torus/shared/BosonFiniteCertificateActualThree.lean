import torus.shared.BosonFiniteCertificateCOM300
import torus.shared.BosonFiniteCertificateCOM301
import torus.shared.BosonFiniteCertificateCOM302
import torus.shared.BosonFiniteCertificateCOM303
import torus.shared.BosonFiniteCertificateCOM304
import torus.shared.BosonFiniteCertificateCOM305
import torus.shared.BosonFiniteCertificateCOM306
import torus.shared.BosonFiniteCertificateCOM307
import torus.shared.BosonFiniteCertificateCOM308
import torus.shared.BosonFiniteCertificateAction
import torus.shared.BosonFiniteCertificateCoordinate
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
variable {K : Type*} [Field K]

theorem p300_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 1, rowOutputOK t.val 0 (p300basis a) = true := by
  decide +kernel

theorem p300_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 1) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p300basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p300basis a) : K) /
        1000000000000) • MvPolynomial.X (0 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p300_all_word_outputs t a)

#print axioms p300_all_word_outputs
#print axioms p300_actual_frozen_row

theorem p301_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 1, rowOutputOK t.val 1 (p301basis a) = true := by
  decide +kernel

theorem p301_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 1) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p301basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p301basis a) : K) /
        1000000000000) • MvPolynomial.X (1 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p301_all_word_outputs t a)

#print axioms p301_all_word_outputs
#print axioms p301_actual_frozen_row

theorem p302_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 2, rowOutputOK t.val 2 (p302basis a) = true := by
  decide +kernel

theorem p302_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 2) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p302basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p302basis a) : K) /
        1000000000000) • MvPolynomial.X (2 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p302_all_word_outputs t a)

#print axioms p302_all_word_outputs
#print axioms p302_actual_frozen_row

theorem p303_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 3, rowOutputOK t.val 3 (p303basis a) = true := by
  decide +kernel

theorem p303_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 3) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p303basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p303basis a) : K) /
        1000000000000) • MvPolynomial.X (3 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p303_all_word_outputs t a)

#print axioms p303_all_word_outputs
#print axioms p303_actual_frozen_row

theorem p304_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 4, rowOutputOK t.val 4 (p304basis a) = true := by
  decide +kernel

theorem p304_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 4) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p304basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p304basis a) : K) /
        1000000000000) • MvPolynomial.X (4 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p304_all_word_outputs t a)

#print axioms p304_all_word_outputs
#print axioms p304_actual_frozen_row

theorem p305_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 5, rowOutputOK t.val 5 (p305basis a) = true := by
  decide +kernel

theorem p305_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 5) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p305basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p305basis a) : K) /
        1000000000000) • MvPolynomial.X (5 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p305_all_word_outputs t a)

#print axioms p305_all_word_outputs
#print axioms p305_actual_frozen_row

theorem p306_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 7, rowOutputOK t.val 6 (p306basis a) = true := by
  decide +kernel

theorem p306_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 7) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p306basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p306basis a) : K) /
        1000000000000) • MvPolynomial.X (6 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p306_all_word_outputs t a)

#print axioms p306_all_word_outputs
#print axioms p306_actual_frozen_row

theorem p307_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 8, rowOutputOK t.val 7 (p307basis a) = true := by
  decide +kernel

theorem p307_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 8) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p307basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p307basis a) : K) /
        1000000000000) • MvPolynomial.X (7 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p307_all_word_outputs t a)

#print axioms p307_all_word_outputs
#print axioms p307_actual_frozen_row

theorem p308_all_word_outputs :
    ∀ t : Fin 4, ∀ a : Fin 10, rowOutputOK t.val 8 (p308basis a) = true := by
  decide +kernel

theorem p308_actual_frozen_row (t : Fin 4)
    (r : Fin (frozenRows t.val).length) (a : Fin 10) :
    paperRowWordOperator t.val ((frozenRows t.val)[r.val]?.getD [])
      (wordPolynomial (p308basis a) : Core ℕ K) =
      ((threeRowAction t.val ((frozenRows t.val)[r.val]?.getD []) (p308basis a) : K) /
        1000000000000) • MvPolynomial.X (8 - t.val) :=
  paperRowWordOperator_apply _ _ _ _ (p308_all_word_outputs t a)

#print axioms p308_all_word_outputs
#print axioms p308_actual_frozen_row

end TorusLean.BosonFiniteCertificate
