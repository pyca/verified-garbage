module

public import VerifiedGarbage.Proof.Camellia.X86.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86.Verified
public import VerifiedGarbage.Proof.Camellia.X86.PreparedVerified
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 Impl.Camellia.X86.expandKey
    stack := 2708
    verified := Proof.Camellia.X86.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt)
    stack := 2728
    verified := Proof.Camellia.X86.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt)
    stack := 2728
    verified := Proof.Camellia.X86.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.X86.layout).artifact X86.target {
    code := Impl.Camellia.X86.cryptPrepared
    verified := Proof.Camellia.X86.crypt_verified }]

end VG.Artifacts.Camellia.X86
