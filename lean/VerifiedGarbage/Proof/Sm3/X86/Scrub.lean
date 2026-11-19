module

public import VerifiedGarbage.Proof.Sm3.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.PostOut
import VerifiedGarbage.Proof.Sm3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm3.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sm3.Contract
meta import VerifiedGarbage.Proof.Sm3.PostOut
meta import VerifiedGarbage.Proof.Sm3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3's streaming functions on x86 (32-bit), without secret residue

`vg_sm3_init`, which calls nothing and has no frame, followed by the clearing
of the registers a callee may change (`X86.Scrub.scrubOf`); `vg_sm3_update`
and `vg_sm3_finalize`, whose working space is in a frame of their own, with
the stack they and the compression function use zeroed first
(`X86.Scrub.scrubFOf`), given that their postconditions read the memory on
return only within the buffers (`Proof.Sm3.PostOut`).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Scrub

open VG.Spec.Sm3 VG.X86 VG.X86.Scrub

theorem updateOut (stack : Nat) : PostOut (updateContract X86.abi stack) (updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sm3.updatePost_out 32)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86.abi stack) (finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sm3.finalizePost_out 32)

/-- `vg_sm3_init`. -/
def initReg : Registration Spec.Sm3.initApi target :=
  scrubOf { code := Impl.Sm3.X86.Stream.init, verified := Shared.init }

/-- `vg_sm3_update`. -/
def updateReg : Registration Spec.Sm3.updateApi target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update
      stack := 20 + 188
      verified := Shared.update }
    (updateOut _)

/-- `vg_sm3_finalize`. -/
def finalizeReg : Registration Spec.Sm3.finalizeApi target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize
      stack := 20 + 184
      verified := Shared.finalize }
    (finalizeOut _)

end VG.Proof.Sm3.X86.Scrub
