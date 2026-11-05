module

public import VerifiedGarbage.Proof.Camellia.X86.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86.Verified
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

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
    verified := Proof.Camellia.X86.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.X86
