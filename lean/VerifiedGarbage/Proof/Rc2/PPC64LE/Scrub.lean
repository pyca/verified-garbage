module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC2 on PPC64LE, without secret residue

`vg_rc2_cbc_init` and the two chained CBC functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), but call
another function inside it (`vg_rc2_expand_key`, `vg_rc2_encrypt_block`,
`vg_rc2_decrypt_block`), whose frame is below theirs. So they are followed
by `Impl.Scrub.PPC64LE.scrubTail` with their stack wiped
(`PPC64LE.Scrub.scrubOf`). Their postconditions read the memory on return
only within their buffers, by the target-independent lemmas RISC-V's proofs
use (`Proof/Rc2/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem cbcInitOut (stack : Nat) : PostOut (Spec.Rc2.cbcInitContract PPC64LE.abi stack) (Spec.Rc2.cbcInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcEncryptChainedContract PPC64LE.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 64))

theorem cbcDecryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcDecryptChainedContract PPC64LE.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 64))

/-! ## The registrations -/

/-- `Spec.Rc2.cbcInitApi`. -/
def cbcInitReg : Registration Spec.Rc2.cbcInitApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.init
      verified := Proof.Rc2.PPC64LE.Stream.init_framed }
    608 ⟨true, true, [.r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13]⟩
    (cbcInitOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Rc2.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Rc2.cbcEncryptChainedApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.encrypt
      verified := Proof.Rc2.PPC64LE.Cbc.encryptChained_framed }
    544 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (cbcEncryptChainedOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Rc2.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Rc2.cbcDecryptChainedApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.decrypt
      verified := Proof.Rc2.PPC64LE.Cbc.decryptChained_framed }
    544 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (cbcDecryptChainedOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Rc2.PPC64LE.Scrub
