import torus.shared.BosonFiniteCertificateNatFourColumnCache416Data

/-! One complete original signed column-Gram channel, checked directly
against all original integer rows and exact original active pair positions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f416_source_gram_cache_channel0 :
    f416sourceGramCache 0=natFourOriginalColumnCache 0 (f416activePairs 0) := by
  decide +kernel

#print axioms f416_source_gram_cache_channel0
end TorusLean.BosonFiniteCertificate
