module

import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AesOcb.RISCV64.Fn
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
(`RISCV64.Scrub.verifiedScrubbed`), which clears the caller-saved registers and all
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

/-- What the cleanup needs of `vg_aes_ocb_init`'s code (`scrubSide`), by the kernel's
evaluation, stated apart from the registration record so that `lit_decide` sees only the
code. -/
theorem init_scrubSide :
    VG.RISCV64.Scrub.scrubSide
      (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init) 2560 0 []
      = true := by
  lit_decide

/-- `vg_aes_ocb_init` as emitted (`Impl.AesOcb.RISCV64.Fn.init`) meets its contract in constant
time and returns without secret residue: the theorem its registration binds. -/
theorem init_scrubbed :
    VerifiedScrubbed VG.RISCV64.target Impl.AesOcb.RISCV64.Fn.init
      (Spec.Ocb.initContract RISCV64.abi 2560) 0 :=
  VG.RISCV64.Scrub.verifiedScrubbed (api := Spec.Ocb.initApi) (W := 2560)
    { code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
      verified := init_framed }
    initOut init_scrubSide

end VG.Proof.AesOcb.RISCV64
