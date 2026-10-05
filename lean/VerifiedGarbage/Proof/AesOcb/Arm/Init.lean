import VerifiedGarbage.Proof.AesGcm.Arm.Frame
import VerifiedGarbage.Spec.Ocb.Contract

/-!
# AES-OCB on ARMv7: the key setup

Untrusted: everything here is checked by Lean. An AES-OCB key context is an
AES-GCM one: the key schedule, then `ENCIPHER(K, zeros(128))` at byte 240
(`L_*` for OCB, the hash subkey for GCM), so `vg_aes_ocb_init` is
`vg_aes_gcm_init`'s code (`Impl.AesGcm.Arm.init`), whose proof
(`Proof.AesGcm.Arm.init_framed`) gives OCB's contract too.
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init)
    (Spec.Ocb.initContract Arm.abi 2568) :=
  Proof.AesGcm.Arm.init_framed.of_implies
    ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, Proof.AesGcm.Arm.initFrameSat_pre⟩

end VG.Proof.AesOcb.Arm
