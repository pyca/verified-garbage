module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.X86.KeyVerified
public import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
public import VerifiedGarbage.Proof.Cast5.X86.FbFinalVerified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# CAST5 on x86 (32-bit), without secret residue

The eleven CAST5 functions as emitted (`Impl.Cast5.X86.Fn`), which return
without secret residue (`X86.Scrub.verifiedScrubbedAll`): each zeroes the stack
its contract reserves below `esp` and clears the registers a callee may
change: the 4 bytes of the call that finds the tables
(`call 2f`) for key expansion and ECB, whose working space is their
caller's `scratch`, and the 336 bytes of the modes' frame and that call.
What the cleanup needs of the code is one Boolean (`X86.Scrub.scrubFSide`),
proved by evaluating the code once (`lit_decide`). Their postconditions read
the memory on return only within the buffers (`X86.Scrub.PostOut`): the
schedule, the data and the chaining block; a length is the low 32 bits of
its argument word.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Cast5.ScrubLocal
open VG.Proof.Aes.ScrubLocal (bytesAt_of0)

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (X86.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (X86.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := lenC x 1
  simpa only [Nat.mul_one, Elem.size] using this

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (X86.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (X86.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The functions as emitted -/

/-- `Spec.Cast5.expandKeyApi` as emitted (`Impl.Cast5.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.expandKey (Spec.Cast5.expandKeyContract (X86.abi.withConsts Impl.Cast5.keyConsts) 4) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.expandKeyApi)
    { code := Impl.Cast5.X86.expandKey
      verified := Proof.Cast5.X86.expandKey_verified }
    (expandKeyOut _)

/-- `Spec.Cast5.ecbEncryptApi` as emitted (`Impl.Cast5.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.ecbEncrypt (Spec.Cast5.ecbEncryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 4) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ecbEncryptApi)
    { code := Impl.Cast5.X86.ecbEncrypt
      verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.X86.ecbEncrypt_verified }
    (ecbOut .encrypt _)

/-- `Spec.Cast5.ecbDecryptApi` as emitted (`Impl.Cast5.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.ecbDecrypt (Spec.Cast5.ecbDecryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 4) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ecbDecryptApi)
    { code := Impl.Cast5.X86.ecbDecrypt
      verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.X86.ecbDecrypt_verified }
    (ecbOut .decrypt _)

/-- `Spec.Cast5.cbcEncryptChainedApi` as emitted (`Impl.Cast5.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cbcEncryptChained (Spec.Cast5.cbcEncryptChainedContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcEncryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.X86.ModeFns.cbcEncryptChained_framed }
    (cbcEncryptOut _)

/-- `Spec.Cast5.cbcDecryptChainedApi` as emitted (`Impl.Cast5.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cbcDecryptChained (Spec.Cast5.cbcDecryptChainedContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcDecryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.X86.ModeFns.cbcDecryptChained_framed }
    (cbcDecryptOut _)

/-- `Spec.Cast5.cfbEncryptApi` as emitted (`Impl.Cast5.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cfbEncrypt (Spec.Cast5.cfbEncryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.X86.ModeFns.cfbEncrypt_framed }
    (cfbEncryptOut _)

/-- `Spec.Cast5.cfbDecryptApi` as emitted (`Impl.Cast5.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cfbDecrypt (Spec.Cast5.cfbDecryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.X86.ModeFns.cfbDecrypt_framed }
    (cfbDecryptOut _)

/-- `Spec.Cast5.cfbEncryptFinalApi` as emitted (`Impl.Cast5.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cfbEncryptFinal (Spec.Cast5.cfbEncryptFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.X86.FbFinal.cfbEncryptFinal_framed }
    (cfbEncryptFinalOut _)

/-- `Spec.Cast5.cfbDecryptFinalApi` as emitted (`Impl.Cast5.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.cfbDecryptFinal (Spec.Cast5.cfbDecryptFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.X86.FbFinal.cfbDecryptFinal_framed }
    (cfbDecryptFinalOut _)

/-- `Spec.Cast5.ofbApi` as emitted (`Impl.Cast5.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.ofb (Spec.Cast5.ofbContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofb
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.X86.ModeFns.ofb_framed }
    (ofbOut _)

/-- `Spec.Cast5.ofbFinalApi` as emitted (`Impl.Cast5.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Cast5.X86.Fn.ofbFinal (Spec.Cast5.ofbFinalContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 336) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.X86.FbFinal.ofbFinal_framed }
    (ofbFinalOut _)

end VG.Proof.Cast5.X86.Scrub
