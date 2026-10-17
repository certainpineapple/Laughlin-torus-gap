import torus.shared.BosonFiniteCertificateNatFourColumnCache411Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache411Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache411Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache411Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f411_source_gram_cache_check : ∀ t : Fin 4,
    f411sourceGramCache t.val=natFourOriginalColumnCache t.val (f411activePairs t.val) := by
  intro t
  fin_cases t
  · exact f411_source_gram_cache_channel0
  · exact f411_source_gram_cache_channel1
  · exact f411_source_gram_cache_channel2
  · exact f411_source_gram_cache_channel3

#print axioms f411_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
