module

public import VerifiedGarbage.Proof.Zeroize.X86_64Avx
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

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
