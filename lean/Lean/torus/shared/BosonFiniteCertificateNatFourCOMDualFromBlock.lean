import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateFamily

/-! Full-COM dual coordinates from actual inner products and the small
relative inverse Grams. These identities are on the complete N4 fixed-degree
carrier: there is no lowering-zero premise on the input polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def natFourCompleteCOMGram (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℂ :=
  (natFourCOMBlockGram D.val (natFourRelativeDimensionAt D)
    (fun d => complexify (natFourRelativeGram (natFourRelativeDegreeAt D d)))).submatrix
      (natFourCOMIndexEquiv D) (natFourCOMIndexEquiv D)

def natFourCompleteCOMGramInverse (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℂ :=
  (natFourCOMBlockInverse D.val (natFourRelativeDimensionAt D)
    (fun d => complexify (natFourRelativeGramInverse (natFourRelativeDegreeAt D d)))).submatrix
      (natFourCOMIndexEquiv D) (natFourCOMIndexEquiv D)

def natFourCompleteCOMDualCoordinates (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℂ :=
  natFourCompleteCOMGramInverse D*(complexify (natFourCompleteCOMCoordinates D))ᴴ*
    complexify (natFourWordGram (natFourOccupationBasis D))

theorem natFourCompleteCOMFamily_bihomogeneous (D : Fin 17)
    (i : Fin (natFourOccupationDimension D)) :
    (natFourCompleteCOMFamily D i).IsHomogeneous 4 ∧
      (natFourCompleteCOMFamily D i).IsWeightedHomogeneous id D.val := by
  rw [natFourCompleteCOMFamily_coordinates]
  exact natFourWordBlock_bihomogeneous_of_enumeration D.val
    (natFourOccupationBasis D) (natFourOccupationBasis_enumeration D) _

theorem natFourCompleteCOMGram_inverse_left (D : Fin 17) :
    natFourCompleteCOMGramInverse D*natFourCompleteCOMGram D=1 := by
  apply natFourCOMBlockInverse_reindexed_left
  intro d
  change complexify (natFourRelativeGramInverse (natFourRelativeDegreeAt D d)) *
    complexify (natFourRelativeGram (natFourRelativeDegreeAt D d)) =
      (1 : Matrix (Fin (natFourRelativeDimension (natFourRelativeDegreeAt D d)))
        (Fin (natFourRelativeDimension (natFourRelativeDegreeAt D d))) ℂ)
  rw [←complexify_mul_rect,natFourRelativeGram_inverse_left,complexify_one_rat]

theorem natFourCompleteCOMGram_inverse_right (D : Fin 17) :
    natFourCompleteCOMGram D*natFourCompleteCOMGramInverse D=1 :=
  mul_eq_one_comm.mp (natFourCompleteCOMGram_inverse_left D)

theorem natFourCompleteCOMCoordinates_gram (D : Fin 17) :
    (complexify (natFourCompleteCOMCoordinates D))ᴴ*
      complexify (natFourWordGram (natFourOccupationBasis D))*
        complexify (natFourCompleteCOMCoordinates D)=natFourCompleteCOMGram D := by
  rw [←complexify_transpose_rect,←complexify_mul_rect,←complexify_mul_rect]
  rw [←natFourCOMFamily_gram (natFourOccupationBasis D)
    (natFourOccupationBasis_injective D) (natFourCompleteCOMFamily D)
    (natFourCompleteCOMCoordinates D) (natFourCompleteCOMFamily_coordinates D)]
  exact natFourCompleteCOMFamily_gram D

theorem natFourCompleteCOMDualCoordinates_left (D : Fin 17) :
    natFourCompleteCOMDualCoordinates D*complexify (natFourCompleteCOMCoordinates D)=1 := by
  calc
    _ = natFourCompleteCOMGramInverse D*
      ((complexify (natFourCompleteCOMCoordinates D))ᴴ*
        complexify (natFourWordGram (natFourOccupationBasis D))*
          complexify (natFourCompleteCOMCoordinates D)) := by
            simp only [natFourCompleteCOMDualCoordinates,Matrix.mul_assoc]
    _ = 1 := by rw [natFourCompleteCOMCoordinates_gram,natFourCompleteCOMGram_inverse_left]

theorem natFourCompleteCOMDualCoordinates_right (D : Fin 17) :
    complexify (natFourCompleteCOMCoordinates D)*natFourCompleteCOMDualCoordinates D=1 :=
  mul_eq_one_comm.mp (natFourCompleteCOMDualCoordinates_left D)

/-- Explicit reconstruction of every actual four-particle polynomial at this
degree by all COM levels and all original relative columns. -/
theorem natFourCompleteCOMFamily_reconstruct (D : Fin 17)
    (x : Fin (natFourOccupationDimension D) → ℂ) :
    natFamilySynthesis (natFourCompleteCOMFamily D)
      (natFourCompleteCOMDualCoordinates D *ᵥ x)=
        natFourWordBlock (natFourOccupationBasis D) x := by
  rw [natFourCOMFamily_synthesis (natFourOccupationBasis D)
    (natFourCompleteCOMFamily D) (natFourCompleteCOMCoordinates D)
    (natFourCompleteCOMFamily_coordinates D),Matrix.mulVec_mulVec,
    natFourCompleteCOMDualCoordinates_right,Matrix.one_mulVec]

/-- Whole-N4 fixed-degree completeness, with no relative-vacuum hypothesis. -/
theorem natFourCompleteCOMFamily_complete (D : Fin 17) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D.val) :
    ∃ x, natFamilySynthesis (natFourCompleteCOMFamily D) x=f := by
  obtain ⟨v,hv⟩ := natFour_homogeneous_eq_block_of_enumeration D.val
    (natFourOccupationBasis D) (natFourOccupationBasis_enumeration D) f hN hd
  exact ⟨natFourCompleteCOMDualCoordinates D *ᵥ v,
    (natFourCompleteCOMFamily_reconstruct D v).trans hv⟩

#print axioms natFourCompleteCOMFamily_bihomogeneous
#print axioms natFourCompleteCOMGram_inverse_left
#print axioms natFourCompleteCOMGram_inverse_right
#print axioms natFourCompleteCOMCoordinates_gram
#print axioms natFourCompleteCOMDualCoordinates_left
#print axioms natFourCompleteCOMDualCoordinates_right
#print axioms natFourCompleteCOMFamily_reconstruct
#print axioms natFourCompleteCOMFamily_complete
end TorusLean.BosonFiniteCertificate
