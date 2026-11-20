module

import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-!
# AES-OCB on RISC-V: the key setup

Untrusted: everything here is checked by Lean. An AES-OCB key context is an
AES-GCM one: the key schedule, then `ENCIPHER(K, zeros(128))` at byte 240
(`L_*` for OCB, the hash subkey for GCM), so `vg_aes_ocb_init` is
`vg_aes_gcm_init`'s code (`Impl.AesGcm.RISCV64.init`), whose proof
(`Proof.AesGcm.RISCV64.init_framed`) gives OCB's contract too. As on PPC64LE
(`Proof/AesOcb/PPC64LE/Init.lean`).

It returns without secret residue followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and all
of its 2560 bytes of stack, which the residue analysis finds may all hold
the key schedule, as `vg_aes_gcm_init`'s registration does
(`Proof/AesGcm/RISCV64/StreamBs.lean`). Its postcondition reads the memory
on return only within the key context, for a key of a length its
precondition allows (`postOut_of_local_pre`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init)
      (Spec.Ocb.initContract RISCV64.abi 2560) :=
  Proof.AesGcm.RISCV64.init_framed.of_implies
    ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, Proof.AesGcm.RISCV64.initFrameSat_pre⟩

theorem initOut :
    VG.RISCV64.Scrub.PostOut (Spec.Ocb.initContract RISCV64.abi 2560) (Spec.Ocb.initSig.retBits 64) :=
  VG.RISCV64.Scrub.postOut_of_local_pre (leak := none) VG.RISCV64.Scrub.ScrubAbi.plain
    (Proof.AesOcb.initPostOut_local _)

/-- `Spec.Ocb.initApi`. -/
def initReg : Registration Spec.Ocb.initApi RISCV64.target :=
  VG.RISCV64.Scrub.scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
      verified := init_framed }
    initOut

end VG.Proof.AesOcb.RISCV64
