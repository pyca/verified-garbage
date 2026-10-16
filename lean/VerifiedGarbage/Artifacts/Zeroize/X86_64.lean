module

public import VerifiedGarbage.Proof.Zeroize.X86_64Avx
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Zeroize.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86_64.zeroize
    verified := Proof.Zeroize.X86_64.verified },
  Spec.Zeroize.zeroizeApi.artifact target {
    suffix := "_avx"
    notes := ["It stores 64 bytes at a time from `ymm0`, and clears the \
      upper halves of the vector registers (`vzeroupper`) before returning."]
    code := Impl.Zeroize.X86_64.zeroizeAvx
    verified := Proof.Zeroize.X86_64.verifiedAvx
    features := ["avx"] }]
end VG.Artifacts.Zeroize.X86_64
