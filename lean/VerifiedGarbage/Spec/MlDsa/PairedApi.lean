module

public import VerifiedGarbage.Spec.MlDsa.PairedResponse

@[expose] public section

namespace VG.Spec.MlDsa

def pairedZApi : Api where
  module := "mldsa"
  name := "vg_mldsa_fused_pair_z"
  sig := pairedZSig
  writeArgs := true
  contracts := some fun A stack => pairedZContract A stack
  summary := "Multiplies and inverse-transforms two challenge products, adds both signed responses, and checks their strict norm bound."
  safety := ["Challenge and secret coefficients must be below 3q; response inputs must be canonical.",
    "The bound must be between 1 and 524288.",
    "Both signed output polynomials are written on acceptance and rejection."]

def pairedLowApi : Api where
  module := "mldsa"
  name := "vg_mldsa_fused_pair_r0"
  sig := pairedLowSig
  writeArgs := true
  contracts := some fun A stack => pairedLowContract A stack
  summary := "Multiplies and inverse-transforms two challenge products, writes the high and signed low parts of both differences, and checks the strict low-part norm bound."
  safety := ["Challenge and secret coefficients must be below 3q; difference inputs must be canonical.",
    "Gamma must be an ML-DSA gamma2 value; the bound must be between 1 and 524288.",
    "Both high and low output pairs are written on acceptance and rejection."]

def pairedHintApi : Api where
  module := "mldsa"
  name := "vg_mldsa_fused_pair_h"
  sig := pairedHintSig
  writeArgs := true
  contracts := some fun A stack => pairedHintContract A stack
  summary := "Multiplies and inverse-transforms two challenge products, constructs both hint polynomials, and returns their total count and strict norm result."
  safety := ["Challenge and secret coefficients must be below 3q.",
    "Low and high inputs must form valid ML-DSA decompositions; the bound must equal gamma2.",
    "Both hint polynomials are written on acceptance and rejection."]

end VG.Spec.MlDsa
