module

-- separate module: the target-independent contracts with the working space and their locality, as `ScratchSplit.lean`, apart from the x86-64 proof that uses them

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-!
# AES-GCM `open_to` with its working space as an argument

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to_prepared`
and `vg_aes_gcm_open_to_prepared16` decrypt long inputs in one pass in a frame
of their own holding their working space (`Verified.stackArgScratch`), around
code proved with it as an argument: the contracts of
`Proof/AesGcm/RoundsTo.lean`, with a 2560-byte `work` buffer appended,
whatever it holds (`Sig.scratchContract`). The frame copies the arguments
passed on the stack, which needs the pre- and postconditions and the leak to
read the memory on entry only within the function's buffers
(`openToPreparedPre_local`, `openToRoundsPost_local`, `openToLeak_local`):
the key context, the nonce, the additional data, `src` and the tag.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- `vg_aes_gcm_open_to_prepared` with `work: *mut [u64; 320]`. -/
def openToPreparedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 320)]
  ret := some .u32

/-- `openToPreparedRoundsContract`, whatever `work` is. -/
def openToPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      Proof.Gcm.openToPowersPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)

/-- `openToPrepared16RoundsContract`, whatever `work` is. -/
def openToPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)

variable (pb : Nat)

theorem openToPreparedPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (Proof.Gcm.openToPowersPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (Proof.Gcm.openToPowersPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPrecomputedSig, openToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.Gcm.openToPowersPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.Gcm.openToPowersPre pb) _ m₂
  dsimp only [Curry.apply, Proof.Gcm.openToPowersPre, ArgWord.ofRaw, IntTy.bits] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowersRepr_congr hc h.2.2⟩

theorem openToPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToPrepared16Pre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPrecomputedSig, openToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, openToPrepared16Pre, ArgWord.ofRaw, IntTy.bits] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowers16Repr_congr hc h.2.2⟩

/-- What `open` computes on the memory `m₂` is what it computes on `m₁`
where they agree on the buffers it reads. -/
theorem openToResult_local {m₁ m₂ : Mem} {ctx rd nonce nl aad al src len tag tl : BitVec 64}
    (hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14)
    (hc : ∀ i < 1024, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hn : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (ha : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hs : ∀ i < len.toNat, m₂ (src + BitVec.ofNat 64 i) = m₁ (src + BitVec.ofNat 64 i))
    (ht : ∀ i < tl.toNat, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    openResult (ctxCiph m₂ ctx (rd.setWidth pb).toNat) (ctxH m₂ ctx) (tl.setWidth pb).toNat
        (Spec.Aes.bytesAt m₂ nonce (nl.setWidth pb).toNat) (Spec.Aes.bytesAt m₂ src (len.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat) (Spec.Aes.bytesAt m₂ tag (tl.setWidth pb).toNat) =
      openResult (ctxCiph m₁ ctx (rd.setWidth pb).toNat) (ctxH m₁ ctx) (tl.setWidth pb).toNat
        (Spec.Aes.bytesAt m₁ nonce (nl.setWidth pb).toNat) (Spec.Aes.bytesAt m₁ src (len.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat) (Spec.Aes.bytesAt m₁ tag (tl.setWidth pb).toNat) := by
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  have := Nat.mod_le tl.toNat (2 ^ pb)
  rw [ctxCiph_congr (le15 hr) fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (p := nonce) (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := aad) (n := (al.setWidth pb).toNat) fun i hi => ha i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := src) (n := (len.setWidth pb).toNat) fun i hi => hs i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := tag) (n := (tl.setWidth pb).toNat) fun i hi => ht i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]

theorem openToRoundsPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPrecomputedSig, openToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2.2)]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToPrecomputedSig.words pb) (openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPrecomputedSig, openToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (openToLeak pb) _ m₂
  dsimp only [Curry.apply, openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
      (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcm
