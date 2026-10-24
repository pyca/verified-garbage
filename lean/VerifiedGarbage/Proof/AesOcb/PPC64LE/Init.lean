module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# AES-OCB on PPC64LE: the key setup

Untrusted: everything here is checked by Lean. An AES-OCB key context is an
AES-GCM one: the key schedule, then `ENCIPHER(K, zeros(128))` at byte 240
(`L_*` for OCB, the hash subkey for GCM), so `vg_aes_ocb_init` is
`vg_aes_gcm_init`'s code (`Impl.AesGcm.PPC64LE.init`), whose proof
(`Proof.AesGcm.PPC64LE.init_framed`) gives OCB's contract too. As on ARMv7
(`Proof/AesOcb/Arm/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init)
      (Spec.Ocb.initContract PPC64LE.abi 2592) :=
  Proof.AesGcm.PPC64LE.init_framed.of_implies
    ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, Proof.AesGcm.PPC64LE.initFrameSat_pre⟩

end VG.Proof.AesOcb.PPC64LE
