import torus.shared.BosonFiniteCertificateNatComparison300
import torus.shared.BosonFiniteCertificateNatComparison301
import torus.shared.BosonFiniteCertificateNatComparison302
import torus.shared.BosonFiniteCertificateNatComparison303
import torus.shared.BosonFiniteCertificateNatComparison304
import torus.shared.BosonFiniteCertificateNatComparison305
import torus.shared.BosonFiniteCertificateNatComparison306
import torus.shared.BosonFiniteCertificateNatComparison307
import torus.shared.BosonFiniteCertificateNatComparison308
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson

/-- The original finite comparison is nonnegative on every low-degree
relative N3 polynomial of the natural-orbital core, with its genuine H squared,
all original rows, and its genuine initial COM descendants. -/
theorem canonicalNatComparisonForm_low_degree_nonneg (d : ℕ) (hd8 : d≤8)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) : 0 ≤ (canonicalNatComparisonForm d f f).re := by
  interval_cases d
  · exact k300_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k301_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k302_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k303_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k304_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k305_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k306_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k307_nat_homogeneous_comparison_nonneg f hN hd hL
  · exact k308_nat_homogeneous_comparison_nonneg f hN hd hL

#print axioms canonicalNatComparisonForm_low_degree_nonneg
end TorusLean.BosonFiniteCertificate
