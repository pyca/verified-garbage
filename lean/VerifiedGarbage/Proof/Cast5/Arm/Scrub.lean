module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Cast5.Arm.Fn
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
public import VerifiedGarbage.Proof.Cast5.Arm.KeyVerified
public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Cast5.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal
import VerifiedGarbage.Proof.Cast5.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Spec.Cast5.Cbc
meta import VerifiedGarbage.Spec.Cast5.Cfb
meta import VerifiedGarbage.Spec.Cast5.Ofb
meta import VerifiedGarbage.Spec.Cast5.CfbFinal
meta import VerifiedGarbage.Spec.Cast5.OfbFinal
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Cast5.Arm.Fn
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.Arm.KeyVerified
meta import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
meta import VerifiedGarbage.Proof.Cast5.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
/-!
# CAST5 on ARMv7, without secret residue

The eleven CAST5 functions with their cleanup (`Impl.Cast5.Arm.Fn`): each
returns with the registers a callee may change set to constants. Key
expansion and ECB keep their working space in their caller's `scratch` and
have no frames (`Arm.Scrub.verifiedScrubbed`, `Code.noFrames` evaluated by
`lit_decide`). The modes keep theirs in a frame of 328 bytes and call ECB's
code, in a frame of 8 more, under a name of its own
(`vg_cast5_ecb_encrypt_entry`, `Impl.Cast5.Arm.ecbCore`), which the emitter
writes as an internal function. They leave their frame as it is, and their
cleanup zeroes the 336 bytes their contracts reserve in a loop
(`Arm.Scrub.verifiedScrubbedAll`, from their frames' size and that they make
no indirect call, `CodeOk`, which the kernel evaluates here: `lit_decide`),
and their postconditions read the memory on return only within the buffers
(`Arm.Scrub.PostOut`): the schedule, the data and the chaining block, as on
x86 (`Proof/Cast5/X86/Scrub.lean`); a length is the low 32 bits of its
argument word.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm VG.Proof.Cast5.ScrubLocal
open VG.Proof.Aes.ScrubLocal (bytesAt_of0)

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (Arm.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (Arm.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := lenC x 1
  simpa only [Nat.mul_one, Elem.size] using this

/-! ## The modes' postconditions -/

theorem cbcEncryptOut :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut :
    PostOut (Spec.Cast5.cfbEncryptContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut :
    PostOut (Spec.Cast5.cfbDecryptContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut :
    PostOut (Spec.Cast5.ofbContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.ofbSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut :
    PostOut (Spec.Cast5.ofbFinalContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336) (Spec.Cast5.ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The code: frames and indirect calls -/

theorem expandKey_noFrames : Impl.Cast5.Arm.expandKey.noFrames = true := by lit_decide
theorem ecbEncrypt_noFrames : Impl.Cast5.Arm.ecbEncrypt.noFrames = true := by lit_decide
theorem ecbDecrypt_noFrames : Impl.Cast5.Arm.ecbDecrypt.noFrames = true := by lit_decide

/-! ## The stack the modes zeroed in a loop use (`scrubAll`, `Arm.Scrub.CodeOk`) -/

theorem cbcEncryptChained_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cbcEncryptChained) 336 := by
  lit_decide
theorem cbcDecryptChained_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cbcDecryptChained) 336 := by
  lit_decide
theorem cfbEncrypt_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbEncrypt) 336 := by
  lit_decide
theorem cfbDecrypt_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbDecrypt) 336 := by
  lit_decide
theorem cfbEncryptFinal_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbEncryptFinal) 336 := by
  lit_decide
theorem cfbDecryptFinal_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbDecryptFinal) 336 := by
  lit_decide
theorem ofb_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.ofb) 336 := by
  lit_decide
theorem ofbFinal_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.ofbFinal) 336 := by
  lit_decide

end VG.Proof.Cast5.Arm.Scrub

namespace VG.Proof.Cast5.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_cast5_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.expandKey
      (Spec.Cast5.expandKeyContract (abi.withConsts Impl.Cast5.keyConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.expandKeyApi)
    { code := Impl.Cast5.Arm.expandKey, verified := Proof.Cast5.Arm.expandKey_verified }
    Scrub.expandKey_noFrames

/-- `vg_cast5_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.ecbEncrypt
      (Spec.Cast5.ecbEncryptContract (abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbEncryptApi)
    { code := Impl.Cast5.Arm.ecbEncrypt
      verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.Arm.ecbEncrypt_verified }
    Scrub.ecbEncrypt_noFrames

/-- `vg_cast5_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.ecbDecrypt
      (Spec.Cast5.ecbDecryptContract (abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbDecryptApi)
    { code := Impl.Cast5.Arm.ecbDecrypt
      verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.Arm.ecbDecrypt_verified }
    Scrub.ecbDecrypt_noFrames

/-- `vg_cast5_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cbcEncryptChained
      (Spec.Cast5.cbcEncryptChainedContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.Arm.cbcEncryptChained_framed }
    Scrub.cbcEncryptOut
    (scrubSideF_of Scrub.cbcEncryptChained_code (by decide) _)

/-- `vg_cast5_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cbcDecryptChained
      (Spec.Cast5.cbcDecryptChainedContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.Arm.cbcDecryptChained_framed }
    Scrub.cbcDecryptOut
    (scrubSideF_of Scrub.cbcDecryptChained_code (by decide) _)

/-- `vg_cast5_cfb64_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cfbEncrypt
      (Spec.Cast5.cfbEncryptContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.Arm.cfbEncrypt_framed }
    Scrub.cfbEncryptOut
    (scrubSideF_of Scrub.cfbEncrypt_code (by decide) _)

/-- `vg_cast5_cfb64_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cfbDecrypt
      (Spec.Cast5.cfbDecryptContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.Arm.cfbDecrypt_framed }
    Scrub.cfbDecryptOut
    (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_cast5_cfb64_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cfbEncryptFinal
      (Spec.Cast5.cfbEncryptFinalContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.Arm.cfbEncryptFinal_framed }
    Scrub.cfbEncryptFinalOut
    (scrubSideF_of Scrub.cfbEncryptFinal_code (by decide) _)

/-- `vg_cast5_cfb64_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.cfbDecryptFinal
      (Spec.Cast5.cfbDecryptFinalContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.Arm.cfbDecryptFinal_framed }
    Scrub.cfbDecryptFinalOut
    (scrubSideF_of Scrub.cfbDecryptFinal_code (by decide) _)

/-- `vg_cast5_ofb`. -/
theorem ofb :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.ofb
      (Spec.Cast5.ofbContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.ofb
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.Arm.ofb_framed }
    Scrub.ofbOut
    (scrubSideF_of Scrub.ofb_code (by decide) _)

/-- `vg_cast5_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.Cast5.Arm.Fn.ofbFinal
      (Spec.Cast5.ofbFinalContract (abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 328 1 Impl.Cast5.Arm.ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.Arm.ofbFinal_framed }
    Scrub.ofbFinalOut
    (scrubSideF_of Scrub.ofbFinal_code (by decide) _)

end VG.Proof.Cast5.Arm.Fn
