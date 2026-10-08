import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchTo
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract

/-! # Prepared-context out-of-place scratch contracts -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm
open VG.Spec.Gcm

abbrev streamEncryptToPreparedScratchSig := streamEncryptToPrecomputedScratchSig

def streamEncryptToPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPreparedPre A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (post := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPost A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (writeArgs := true) (stack := stack)


abbrev sealGatherPreparedScratchSig := sealGatherPrecomputedScratchSig

def sealGatherPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPreparedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (writeArgs := true) (stack := stack)

variable (pb : Nat)

theorem streamEncryptToPreparedPre_local : ∀ vs m₁ m₂,
    vs.length = (streamEncryptToPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToPreparedSig.words pb) (streamEncryptToPreparedPre pb) vs m₁ →
      Curry.apply (streamEncryptToPreparedSig.words pb) (streamEncryptToPreparedPre pb) vs m₂
  | [ctx, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, h => by
    simp only [streamEncryptToPreparedSig, streamEncryptToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPreparedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPreparedPre pb) _ m₂
    dsimp only [Curry.apply, streamEncryptToPreparedPre, ArgWord.ofRaw] at h ⊢
    exact ⟨h.1, h.2.1, preparedPowersRepr_congr hc h.2.2⟩

theorem sealGatherPreparedPre_local : ∀ vs m₁ m₂, vs.length = (sealGatherPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPreparedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPreparedSig.words pb) (sealGatherPreparedPre pb) vs m₁ →
      Curry.apply (sealGatherPreparedSig.words pb) (sealGatherPreparedPre pb) vs m₂
  | [_, _, _, _, _, _, src, cnt, _, _, _], m₁, m₂, _, hb, hl, h => by
    simp only [sealGatherPreparedSig, sealGatherPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [sealGatherPreparedSig, sealGatherPrecomputedSig, Sig.lists, List.append_nil] at hl
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPreparedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (sealGatherPreparedPre pb) _ m₂
    dsimp only [Curry.apply, sealGatherPreparedPre, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le cnt.toNat (2 ^ pb)
    rw [gatheredLen_congr_le (by rw [BitVec.toNat_setWidth]; exact this) hl]
    exact ⟨h.1, h.2.1, preparedPowersRepr_congr hc h.2.2⟩


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

end VG.Proof.AesGcm
