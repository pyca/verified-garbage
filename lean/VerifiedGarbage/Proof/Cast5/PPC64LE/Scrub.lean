module

public import VerifiedGarbage.Impl.Cast5.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# CAST5 on PPC64LE, without secret residue

Key expansion and ECB, which have no frames, are followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which wipes no
stack for them. The CBC, CFB64 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the volatile
registers they write after them (`PPC64LE.Scrub.verifiedScrubbedWiped`). Their
postconditions read the memory on return only within their buffers, as
x86-64's proofs show (`Proof/Cast5/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

private theorem blocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.blocksAt m₂ p n = Spec.Cast5.blocksAt m₁ p n := by
  simp only [Spec.Cast5.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  apply Vector.ext
  intro j hj
  simp only [Spec.Cast5.blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this, hj])

private theorem cbcBlocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.cbcBlocksAt m₂ p n = Spec.Cast5.cbcBlocksAt m₁ p n := by
  simp only [Spec.Cast5.cbcBlocksAt, blocksAt_of0 h hn]

private theorem scheduleAt_of (h : ∀ a, Region.Contains ⟨p, 128⟩ a 1 → m₁ a = m₂ a) :
    Spec.Cast5.scheduleAt m₂ p = Spec.Cast5.scheduleAt m₁ p :=
  Proof.Cast5.scheduleAt_congr (agree_le h (Nat.le_refl _))

end

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (PPC64LE.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
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

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
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

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
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

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
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

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 64) :=
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

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
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

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
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

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 64) :=
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

/-! ## The functions as emitted -/

/-- `vg_cast5_expand_key` as emitted (`Impl.Cast5.PPC64LE.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.expandKey
      (Spec.Cast5.expandKeyContract (PPC64LE.abi.withConsts Impl.Cast5.keyConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.expandKeyApi) { code := Impl.Cast5.PPC64LE.expandKey, verified := Proof.Cast5.PPC64LE.expandKey_verified }
    0 ⟨true, true, [.r4, .r5, .r7, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ (expandKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_cast5_ecb_encrypt` as emitted (`Impl.Cast5.PPC64LE.Fn.ecbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.ecbEncrypt
      (Spec.Cast5.ecbEncryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbEncryptApi) { code := Impl.Cast5.PPC64LE.ecbEncrypt, verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.PPC64LE.ecbEncrypt_verified }
    0 ⟨true, false, [.r5, .r6, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ (ecbOut .encrypt _)
    (by dsimp only; lit_decide)

/-- `vg_cast5_ecb_decrypt` as emitted (`Impl.Cast5.PPC64LE.Fn.ecbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.ecbDecrypt
      (Spec.Cast5.ecbDecryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbDecryptApi) { code := Impl.Cast5.PPC64LE.ecbDecrypt, verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.PPC64LE.ecbDecrypt_verified }
    0 ⟨true, false, [.r5, .r6, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ (ecbOut .decrypt _)
    (by dsimp only; lit_decide)

/-- `vg_cast5_cbc_encrypt_chained` as emitted
(`Impl.Cast5.PPC64LE.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cbcEncryptChained
      (Spec.Cast5.cbcEncryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cbcEncryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.PPC64LE.Modes.cbcEncryptChained_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_cbc_decrypt_chained` as emitted
(`Impl.Cast5.PPC64LE.Fn.cbcDecryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cbcDecryptChained
      (Spec.Cast5.cbcDecryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cbcDecryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.PPC64LE.Modes.cbcDecryptChained_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_cfb64_encrypt` as emitted (`Impl.Cast5.PPC64LE.Fn.cfbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cfbEncrypt
      (Spec.Cast5.cfbEncryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cfbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbEncrypt_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_cfb64_decrypt` as emitted (`Impl.Cast5.PPC64LE.Fn.cfbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cfbDecrypt
      (Spec.Cast5.cfbDecryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cfbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbDecrypt_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_cfb64_encrypt_final` as emitted
(`Impl.Cast5.PPC64LE.Fn.cfbEncryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cfbEncryptFinal
      (Spec.Cast5.cfbEncryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cfbEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_cfb64_decrypt_final` as emitted
(`Impl.Cast5.PPC64LE.Fn.cfbDecryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.cfbDecryptFinal
      (Spec.Cast5.cfbDecryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.cfbDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_ofb` as emitted (`Impl.Cast5.PPC64LE.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.ofb
      (Spec.Cast5.ofbContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.ofbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofb
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.PPC64LE.Modes.ofb_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `vg_cast5_ofb_final` as emitted (`Impl.Cast5.PPC64LE.Fn.ofbFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Cast5.PPC64LE.Fn.ofbFinal
      (Spec.Cast5.ofbFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) 208) 0 :=
  verifiedScrubbedWiped (api := Spec.Cast5.ofbFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.PPC64LE.FbFinal.ofbFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Cast5.PPC64LE.Scrub
