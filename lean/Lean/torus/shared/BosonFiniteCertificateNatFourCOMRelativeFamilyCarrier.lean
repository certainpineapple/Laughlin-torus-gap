import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamilyData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRelativeColumn_bihomogeneous (d : Fin 17)
    (a : Fin (natFourRelativeDimension d)) :
    (natFourRelativeColumn d a).IsHomogeneous 4 ∧
      (natFourRelativeColumn d a).IsWeightedHomogeneous id d.val := by
  fin_cases d
  · exact natFourWordBlock_bihomogeneous_of_enumeration 0 f400basis
      f400_basis_enumeration (fun b => complexify b400relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 1 f401basis
      f401_basis_enumeration (fun b => complexify b401relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 2 f402basis
      f402_basis_enumeration (fun b => complexify b402relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 3 f403basis
      f403_basis_enumeration (fun b => complexify b403relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 4 f404basis
      f404_basis_enumeration (fun b => complexify b404relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 5 f405basis
      f405_basis_enumeration (fun b => complexify b405relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 6 f406basis
      f406_basis_enumeration (fun b => complexify b406relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 7 f407basis
      f407_basis_enumeration (fun b => complexify b407relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 8 f408basis
      f408_basis_enumeration (fun b => complexify b408relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 9 f409basis
      f409_basis_enumeration (fun b => complexify b409relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 10 f410basis
      f410_basis_enumeration (fun b => complexify b410relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 11 f411basis
      f411_basis_enumeration (fun b => complexify b411relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 12 f412basis
      f412_basis_enumeration (fun b => complexify b412relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 13 f413basis
      f413_basis_enumeration (fun b => complexify b413relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 14 f414basis
      f414_basis_enumeration (fun b => complexify b414relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 15 f415basis
      f415_basis_enumeration (fun b => complexify b415relative b a)
  · exact natFourWordBlock_bihomogeneous_of_enumeration 16 f416basis
      f416_basis_enumeration (fun b => complexify b416relative b a)

#print axioms natFourRelativeColumn_bihomogeneous

theorem natFourRelativeColumn_lower (d : Fin 17)
    (a : Fin (natFourRelativeDimension d)) :
    canonicalCOMLowerNat (natFourRelativeColumn d a)=0 := by
  fin_cases d
  · apply (f400_actual_relative_kernel (fun b => complexify b400relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b400relative) a
  · apply (f401_actual_relative_kernel (fun b => complexify b401relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b401relative) a
  · apply (f402_actual_relative_kernel (fun b => complexify b402relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b402relative) a
  · apply (f403_actual_relative_kernel (fun b => complexify b403relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b403relative) a
  · apply (f404_actual_relative_kernel (fun b => complexify b404relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b404relative) a
  · apply (f405_actual_relative_kernel (fun b => complexify b405relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b405relative) a
  · apply (f406_actual_relative_kernel (fun b => complexify b406relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b406relative) a
  · apply (f407_actual_relative_kernel (fun b => complexify b407relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b407relative) a
  · apply (f408_actual_relative_kernel (fun b => complexify b408relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b408relative) a
  · apply (f409_actual_relative_kernel (fun b => complexify b409relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b409relative) a
  · apply (f410_actual_relative_kernel (fun b => complexify b410relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b410relative) a
  · apply (f411_actual_relative_kernel (fun b => complexify b411relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b411relative) a
  · apply (f412_actual_relative_kernel (fun b => complexify b412relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b412relative) a
  · apply (f413_actual_relative_kernel (fun b => complexify b413relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b413relative) a
  · apply (f414_actual_relative_kernel (fun b => complexify b414relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b414relative) a
  · apply (f415_actual_relative_kernel (fun b => complexify b415relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b415relative) a
  · apply (f416_actual_relative_kernel (fun b => complexify b416relative b a)).mpr
    refine ⟨Pi.single a 1,?_⟩
    exact Matrix.mulVec_single_one (complexify b416relative) a

#print axioms natFourRelativeColumn_lower
end TorusLean.BosonFiniteCertificate
