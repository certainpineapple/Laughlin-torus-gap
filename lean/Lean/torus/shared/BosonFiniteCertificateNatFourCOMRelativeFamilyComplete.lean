import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamilyData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRelativeColumn_complete (d : Fin 17) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d.val)
    (hL : canonicalCOMLowerNat f=0) :
    ∃ x, natFamilySynthesis (natFourRelativeColumn d) x=f := by
  fin_cases d
  · obtain ⟨x,hx⟩ := (f400_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f400basis b400relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f401_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f401basis b401relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f402_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f402basis b402relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f403_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f403basis b403relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f404_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f404basis b404relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f405_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f405basis b405relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f406_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f406basis b406relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f407_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f407basis b407relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f408_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f408basis b408relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f409_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f409basis b409relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f410_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f410basis b410relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f411_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f411basis b411relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f412_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f412basis b412relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f413_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f413basis b413relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f414_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f414basis b414relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f415_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f415basis b415relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx
  · obtain ⟨x,hx⟩ := (f416_actual_relative_complete f hN hd).mp hL
    refine ⟨x,?_⟩
    change natFamilySynthesis (natFourColumnFamily f416basis b416relative) x=f
    rw [natFourColumnFamily_synthesis]
    exact hx

#print axioms natFourRelativeColumn_complete
end TorusLean.BosonFiniteCertificate
