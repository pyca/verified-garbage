module

import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-OCB on RISC-V: the key setup

Untrusted: everything here is checked by Lean. An AES-OCB key context is an
AES-GCM one: the key schedule, then `ENCIPHER(K, zeros(128))` at byte 240
(`L_*` for OCB, the hash subkey for GCM), so `vg_aes_ocb_init` is
`vg_aes_gcm_init`'s code (`Impl.AesGcm.RISCV64.init`), whose proof
(`Proof.AesGcm.RISCV64.init_framed`) gives OCB's contract too. As on PPC64LE
(`Proof/AesOcb/PPC64LE/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init)
      (Spec.Ocb.initContract RISCV64.abi 2560) :=
  Proof.AesGcm.RISCV64.init_framed.of_implies
    ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, Proof.AesGcm.RISCV64.initFrameSat_pre⟩

end VG.Proof.AesOcb.RISCV64
