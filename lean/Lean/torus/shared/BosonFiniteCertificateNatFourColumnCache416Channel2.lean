import torus.shared.BosonFiniteCertificateNatFourColumnCache416Data

/-! One complete original signed column-Gram channel, checked directly
against all original integer rows and exact original active pair positions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f416_source_gram_cache_channel2 :
    f416sourceGramCache 2=natFourOriginalColumnCache 2 (f416activePairs 2) := by
  decide +kernel

#print axioms f416_source_gram_cache_channel2
end TorusLean.BosonFiniteCertificate
