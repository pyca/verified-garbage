import VerifiedGarbage.Proof.AesGcm.ScratchP
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM streaming encryption out of place: the conditions read only the buffers

Untrusted: everything here is checked by Lean. A frame that copies the
arguments passed on the stack (`Verified.stackArgScratch`) needs the pre-
and postconditions of `vg_aes_gcm_stream_encrypt_to` and
`vg_aes_gcm_stream_encrypt_to_precomputed` to read the memory on entry only
within their buffers: the key context, the streaming state (through
`StreamRepr`, `streamRepr_congr`) and the input.
-/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

variable (pb : Nat)

theorem streamEncryptToPre_local : ∀ vs m₁ m₂, vs.length = (streamEncryptToSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToSig.words pb) (streamEncryptToPre pb) vs m₁ →
      Curry.apply (streamEncryptToSig.words pb) (streamEncryptToPre pb) vs m₂
  | [_, _, _, _, _, _, _, _, _], _, _, _, _, h => h

theorem streamEncryptToPrecomputedPre_local : ∀ vs m₁ m₂,
    vs.length = (streamEncryptToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToPrecomputedSig.words pb) (streamEncryptToPrecomputedPre pb) vs m₁ →
      Curry.apply (streamEncryptToPrecomputedSig.words pb) (streamEncryptToPrecomputedPre pb) vs m₂
  | [ctx, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, h => by
    simp only [streamEncryptToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPrecomputedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPrecomputedPre pb) _ m₂
    dsimp only [Curry.apply, streamEncryptToPrecomputedPre, ArgWord.ofRaw] at h ⊢
    exact ⟨h.1, h.2.1, powersRepr_congr hc h.2.2⟩

theorem streamEncryptToPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamEncryptToSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToSig.words pb) (streamEncryptToPost pb) vs m₁ m' r →
      Curry.apply (streamEncryptToSig.words pb) (streamEncryptToPost pb) vs m₂ m' r
  | [ctx, _, st, _, _, src, len, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [streamEncryptToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hs := agree_of hb.2.1
    have hd := agree_of hb.2.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamEncryptToPost, ArgWord.ofRaw] at h ⊢
    intro hn iv a p hr hl ht
    have := Nat.mod_le len.toNat (2 ^ pb)
    have hn' := le15 hn
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
    exact h hn iv a p (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

theorem streamEncryptToPrecomputedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamEncryptToPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToPrecomputedSig.words pb) (streamEncryptToPost pb) vs m₁ m' r →
      Curry.apply (streamEncryptToPrecomputedSig.words pb) (streamEncryptToPost pb) vs m₂ m' r
  | [ctx, _, st, _, _, src, len, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [streamEncryptToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hs := agree_of hb.2.1
    have hd := agree_of hb.2.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamEncryptToPost, ArgWord.ofRaw] at h ⊢
    intro hn iv a p hr hl ht
    have := Nat.mod_le len.toNat (2 ^ pb)
    have hn' := le15 hn
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
    exact h hn iv a p (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

end VG.Proof.AesGcm
