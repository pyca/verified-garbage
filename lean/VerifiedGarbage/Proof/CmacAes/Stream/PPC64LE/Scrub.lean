module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming AES-CMAC on PPC64LE, without secret residue

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which
clears the volatile registers they may write and the stack their frames used:
they keep their working space, the key schedule among it, in a 2336-byte
frame they do not wipe themselves (`withStackScratch`). Their postconditions
read the memory on return only within the state and the tag, by the
target-independent lemmas RISC-V's proofs use
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) : PostOut (Spec.Cmac.aesInitContract PPC64LE.abi stack) (Spec.Cmac.aesInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacAes.Stream.initPostOut_local _)

theorem absorbOut (stack : Nat) : PostOut (Spec.Cmac.aesAbsorbContract PPC64LE.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacAes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) : PostOut (Spec.Cmac.aesFinishContract PPC64LE.abi stack) (Spec.Cmac.aesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacAes.Stream.finishPostOut_local _)

/-! ## The registrations -/

/-- `Spec.Cmac.aesInitApi`. -/
def initReg : Registration Spec.Cmac.aesInitApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r6 Impl.CmacAes.Stream.PPC64LE.init
      verified := Proof.CmacAes.Stream.PPC64LE.init_framed }
    2336 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Cmac.aesAbsorbApi`. -/
def absorbReg : Registration Spec.Cmac.aesAbsorbApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r8 Impl.CmacAes.Stream.PPC64LE.absorb
      verified := Proof.CmacAes.Stream.PPC64LE.absorb_framed }
    2336 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (absorbOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Cmac.aesFinishApi`. -/
def finishReg : Registration Spec.Cmac.aesFinishApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r7 Impl.CmacAes.Stream.PPC64LE.finish
      verified := Proof.CmacAes.Stream.PPC64LE.finish_framed }
    2336 ⟨true, false, [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (finishOut _)
    (by dsimp only; lit_decide)

end VG.Proof.CmacAes.Stream.PPC64LE.Scrub
