module

import VerifiedGarbage.Proof.AesGcm.Arm.Frame
public import VerifiedGarbage.Spec.Ocb.Contract
public import Batteries.Logic
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Arm.Target

/-!
# AES-OCB on ARMv7: the key setup

Untrusted: everything here is checked by Lean. An AES-OCB key context is an
AES-GCM one: the key schedule, then `ENCIPHER(K, zeros(128))` at byte 240
(`L_*` for OCB, the hash subkey for GCM), so `vg_aes_ocb_init` is
`vg_aes_gcm_init`'s code (`Impl.AesGcm.Arm.init`), whose proof
(`Proof.AesGcm.Arm.init_framed`) gives OCB's contract too.
-/

@[expose] public section

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init)
    (Spec.Ocb.initContract Arm.abi 2568) :=
  Proof.AesGcm.Arm.init_framed.of_implies
    ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h, Proof.AesGcm.Arm.initFrameSat_pre⟩

end VG.Proof.AesOcb.Arm
