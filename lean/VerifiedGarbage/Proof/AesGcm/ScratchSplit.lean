module
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# AES-GCM `seal_split` with its working space as an argument

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_split` and
its precomputed and prepared forms keep their working space in a frame of
their own (`Verified.stackArgScratch`), around code proved with it as an
argument: `sealSplitScratchContract`, … are the shared contracts with a
2560-byte `work` buffer appended, whatever it holds. The frame copies the
arguments passed on the stack, which needs the pre- and postconditions to
read the memory on entry only within the function's buffers
(`sealSplitPre_local`, `sealSplitPost_local`, …): the key context, the
nonce, the additional data, `src` and `dst`.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec.Gcm Proof.Gcm

/-- `vg_aes_gcm_seal_split` with `work: *mut [u64; 320]`. -/
def sealSplitScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "src_len"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("work", .array true .u64 320)]

/-- `sealSplitContract`, whatever `work` is. -/
def sealSplitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_split_precomputed` with `work: *mut [u64; 320]`. -/
def sealSplitPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "src_len"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("work", .array true .u64 320)]

/-- `sealSplitPrecomputedContract`, whatever `work` is. -/
def sealSplitPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPrecomputedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPrecomputedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_split_prepared` with `work: *mut [u64; 320]`. -/
abbrev sealSplitPreparedScratchSig := sealSplitPrecomputedScratchSig

/-- `sealSplitPreparedContract`, whatever `work` is. -/
def sealSplitPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPreparedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (writeArgs := true) (stack := stack)

variable (pb : Nat)

theorem sealSplitPre_local : ∀ vs m₁ m₂, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₁ →
      Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem sealSplitPrecomputedPre_local : ∀ vs m₁ m₂, vs.length = (sealSplitPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitPrecomputedSig.words pb) (sealSplitPrecomputedPre pb) vs m₁ →
      Curry.apply (sealSplitPrecomputedSig.words pb) (sealSplitPrecomputedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrecomputedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrecomputedPre pb) _ m₂
  dsimp only [Curry.apply, sealSplitPrecomputedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, powersRepr_congr hc h.2.2⟩

theorem sealSplitPreparedPre_local : ∀ vs m₁ m₂, vs.length = (sealSplitPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPreparedPre pb) vs m₁ →
      Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPreparedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitPreparedSig, sealSplitPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPreparedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPreparedPre pb) _ m₂
  dsimp only [Curry.apply, sealSplitPreparedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowersRepr_congr hc h.2.2⟩

/-- `sealSplitPost` reads the memory on entry only within the buffers, for a
key context of `cl ≥ 256` bytes. -/
private theorem post_local {cl : Nat} (hcl : 256 ≤ cl) {m₁ m₂ m' : Mem}
    {ctx rd nonce nl aad al src sl dst len tag : BitVec 64}
    (hc : ∀ i < cl, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hn : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (ha : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hs : ∀ i < sl.toNat, m₂ (src + BitVec.ofNat 64 i) = m₁ (src + BitVec.ofNat 64 i))
    (hd : ∀ i < len.toNat, m₂ (dst + BitVec.ofNat 64 i) = m₁ (dst + BitVec.ofNat 64 i))
    (h : ((rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14) →
      (sl.setWidth pb).toNat ≤ (len.setWidth pb).toNat →
      encryptWith (ctxCiph m₁ ctx (rd.setWidth pb).toNat) (ctxH m₁ ctx) 16
          (Spec.Aes.bytesAt m₁ nonce (nl.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₁ src (sl.setWidth pb).toNat ++
            (Spec.Aes.bytesAt m₁ dst (len.setWidth pb).toNat).drop (sl.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat) =
        (Spec.Aes.bytesAt m' dst (len.setWidth pb).toNat, Spec.Aes.bytesAt m' tag 16)) :
    ((rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14) →
      (sl.setWidth pb).toNat ≤ (len.setWidth pb).toNat →
      encryptWith (ctxCiph m₂ ctx (rd.setWidth pb).toNat) (ctxH m₂ ctx) 16
          (Spec.Aes.bytesAt m₂ nonce (nl.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₂ src (sl.setWidth pb).toNat ++
            (Spec.Aes.bytesAt m₂ dst (len.setWidth pb).toNat).drop (sl.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat) =
        (Spec.Aes.bytesAt m' dst (len.setWidth pb).toNat, Spec.Aes.bytesAt m' tag 16) := by
  intro hr hle
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le sl.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [ctxCiph_congr (le15 hr) fun i hi => hc i (by omega_arith), ctxH_congr fun i hi => hc i (by omega_arith),
    bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (n := (al.setWidth pb).toNat) fun i hi => ha i (by rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (p := src) (n := (sl.setWidth pb).toNat) fun i hi => hs i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (p := dst) (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hr hle

theorem sealSplitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₁ m' r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  exact post_local pb (Nat.le_refl _) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.1) h

theorem sealSplitPrecomputedPost_local : ∀ vs m₁ m₂ m' r,
    vs.length = (sealSplitPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitPrecomputedSig.words pb) (sealSplitPost pb) vs m₁ m' r →
      Curry.apply (sealSplitPrecomputedSig.words pb) (sealSplitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  exact post_local pb (by decide) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.1) h

end VG.Proof.AesGcm
