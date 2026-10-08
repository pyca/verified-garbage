import VerifiedGarbage.Proof.AesGcm.ScratchP
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM one-shot encryption out of place, from a list of slices: the conditions read only the buffers

Untrusted: everything here is checked by Lean. A frame that copies the
arguments passed on the stack (`Verified.stackArgScratchL`) needs the pre-
and postconditions of `vg_aes_gcm_seal_gather` and
`vg_aes_gcm_seal_gather_precomputed` to read the memory on entry only within
their buffers and their list of slices: the key context, the nonce, the
additional data, and the descriptors and the slices they list
(`gathered_congr_le`, `gatheredLen_congr_le`). The contracts take the
number of slices cut to the width of a pointer, at most the one the list is
made of, so this holds for any width.
-/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- The first `N'` of `N` descriptors, where two memories agree on the
descriptors and the slices: they list the same slices, on which the
memories agree. -/
theorem listed_congr_le {pb : Nat} {m₁ m₂ : Mem} {p : Addr} {N' N : Nat} (hle : N' ≤ N)
    (h : ∀ r ∈ Sig.descRegion pb p N :: Sig.listed pb m₁ .u8 p N, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    Sig.listed pb m₂ .u8 p N' = Sig.listed pb m₁ .u8 p N' ∧
      ∀ r ∈ Sig.listed pb m₁ .u8 p N', ∀ a, r.Contains a 1 → m₁ a = m₂ a := by
  refine ⟨(Sig.listed_congr pb .u8 p N' fun a ha => h _ List.mem_cons_self a ?_).symm, fun r hr a ha => ?_⟩
  · simp only [Sig.descRegion, Region.Contains] at ha ⊢
    exact Nat.lt_of_lt_of_le ha (Nat.mul_le_mul_right _ hle)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact h _ (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) hle), rfl⟩)) a ha

theorem gathered_congr_le {pb : Nat} {m₁ m₂ : Mem} {p : Addr} {N' N : Nat} (hle : N' ≤ N)
    (h : ∀ r ∈ Sig.descRegion pb p N :: Sig.listed pb m₁ .u8 p N, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    gathered pb m₂ p N' = gathered pb m₁ p N' := by
  obtain ⟨hl, hr⟩ := listed_congr_le hle h
  simp only [gathered]
  rw [hl, List.flatMap_def, List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left fun r hm => bytesAt_congr (agree_of (hr r hm)))

theorem gatheredLen_congr_le {pb : Nat} {m₁ m₂ : Mem} {p : Addr} {N' N : Nat} (hle : N' ≤ N)
    (h : ∀ r ∈ Sig.descRegion pb p N :: Sig.listed pb m₁ .u8 p N, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    gatheredLen pb m₂ p N' = gatheredLen pb m₁ p N' := by
  simp only [gatheredLen]
  rw [(listed_congr_le hle h).1]

variable (pb : Nat)

theorem sealGatherPre_local : ∀ vs m₁ m₂, vs.length = (sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherSig.words pb) (sealGatherPre pb) vs m₁ →
      Curry.apply (sealGatherSig.words pb) (sealGatherPre pb) vs m₂
  | [_, _, _, _, _, _, src, cnt, _, _, _], m₁, m₂, _, _, hl, h => by
    simp only [sealGatherSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPre pb) _ m₂
    dsimp only [Curry.apply, sealGatherPre, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le cnt.toNat (2 ^ pb)
    rw [gatheredLen_congr_le (by rw [BitVec.toNat_setWidth]; exact this) hl]
    exact h

theorem sealGatherPrecomputedPre_local : ∀ vs m₁ m₂, vs.length = (sealGatherPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPrecomputedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPrecomputedSig.words pb) (sealGatherPrecomputedPre pb) vs m₁ →
      Curry.apply (sealGatherPrecomputedSig.words pb) (sealGatherPrecomputedPre pb) vs m₂
  | [_, _, _, _, _, _, src, cnt, _, _, _], m₁, m₂, _, hb, hl, h => by
    simp only [sealGatherPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [sealGatherPrecomputedSig, Sig.lists, List.append_nil] at hl
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPrecomputedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPrecomputedPre pb) _ m₂
    dsimp only [Curry.apply, sealGatherPrecomputedPre, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le cnt.toNat (2 ^ pb)
    rw [gatheredLen_congr_le (by rw [BitVec.toNat_setWidth]; exact this) hl]
    exact ⟨h.1, h.2.1, powersRepr_congr hc h.2.2⟩

/-- `sealGatherPost` reads the memory on entry only within the buffers and the
list of slices, for a key context of `cl ≥ 256` bytes. -/
private theorem post_local {cl : Nat} (hcl : 256 ≤ cl) {m₁ m₂ m' : Mem}
    {ctx rd nonce nl aad al src cnt dst len tag : BitVec 64}
    (hc : ∀ i < cl, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hn : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (ha : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hl : ∀ r ∈ Sig.descRegion pb src cnt.toNat :: Sig.listed pb m₁ .u8 src cnt.toNat,
      ∀ a, r.Contains a 1 → m₁ a = m₂ a)
    (h : ((rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14) →
      gatheredLen pb m₁ src (cnt.setWidth pb).toNat = (len.setWidth pb).toNat →
      encryptWith (ctxCiph m₁ ctx (rd.setWidth pb).toNat) (ctxH m₁ ctx) 16
          (Spec.Aes.bytesAt m₁ nonce (nl.setWidth pb).toNat) (gathered pb m₁ src (cnt.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat) =
        (Spec.Aes.bytesAt m' dst (len.setWidth pb).toNat, Spec.Aes.bytesAt m' tag 16)) :
    ((rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14) →
      gatheredLen pb m₂ src (cnt.setWidth pb).toNat = (len.setWidth pb).toNat →
      encryptWith (ctxCiph m₂ ctx (rd.setWidth pb).toNat) (ctxH m₂ ctx) 16
          (Spec.Aes.bytesAt m₂ nonce (nl.setWidth pb).toNat) (gathered pb m₂ src (cnt.setWidth pb).toNat)
          (Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat) =
        (Spec.Aes.bytesAt m' dst (len.setWidth pb).toNat, Spec.Aes.bytesAt m' tag 16) := by
  intro hr hg
  have := Nat.mod_le cnt.toNat (2 ^ pb)
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have hle : (cnt.setWidth pb).toNat ≤ cnt.toNat := by rw [BitVec.toNat_setWidth]; omega
  rw [gatheredLen_congr_le hle hl] at hg
  rw [ctxCiph_congr (le15 hr) fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (n := (al.setWidth pb).toNat) fun i hi => ha i (by rw [BitVec.toNat_setWidth] at hi; omega),
    gathered_congr_le hle hl]
  exact h hr hg

theorem sealGatherPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherSig.words pb) (sealGatherPost pb) vs m₁ m' r →
      Curry.apply (sealGatherSig.words pb) (sealGatherPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, src, cnt, dst, len, tag], m₁, m₂, m', r, _, hb, hl, h => by
    simp only [sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [sealGatherSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPost pb) _ m₂ m' r
    dsimp only [Curry.apply, sealGatherPost, ArgWord.ofRaw] at h ⊢
    exact post_local pb (Nat.le_refl _) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) hl h

theorem sealGatherPrecomputedPost_local : ∀ vs m₁ m₂ m' r,
    vs.length = (sealGatherPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPrecomputedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPrecomputedSig.words pb) (sealGatherPost pb) vs m₁ m' r →
      Curry.apply (sealGatherPrecomputedSig.words pb) (sealGatherPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, src, cnt, dst, len, tag], m₁, m₂, m', r, _, hb, hl, h => by
    simp only [sealGatherPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [sealGatherPrecomputedSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPost pb) _ m₂ m' r
    dsimp only [Curry.apply, sealGatherPost, ArgWord.ofRaw] at h ⊢
    exact post_local pb (by decide) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) hl h

end VG.Proof.AesGcm
