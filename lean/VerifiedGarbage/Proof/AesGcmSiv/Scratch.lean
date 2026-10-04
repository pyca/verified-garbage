import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch

/-!
# AES-GCM-SIV with its working space as an argument

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` keep their working space in
a frame of their own (`Verified.stackArgScratch`), around code proved with
the working space as a last argument: `sealScratchContract n` and
`openScratchContract n` are the shared contracts with a `work` buffer of `n`
words appended, whatever it holds (each target lays out its own).

The frame also holds a copy of the arguments passed on the stack, which
needs the pre- and postconditions, and `open`'s leak, to read the memory on
entry only within the function's buffers (`sealPost_local`,
`openPost_local`, `openLeak_local`): the nonce, the additional data, the
data, the tag and, for `rounds` of 10 or 14, the round keys in the key
schedule's 240 bytes (`ctxCiph_congr`).
-/

namespace VG.Proof.AesGcmSiv

open VG.Spec.GcmSiv
open VG.Proof.AesGcm (bytesAt_congr agree_of)

/-- `vg_aes_gcm_siv_seal` with `work: *mut [u64; n]`. -/
def sealScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16), ("work", .array true .u64 n)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (sealScratchSig n).contract A
    (pre := fun sch rounds nonce aad aadLen data len tag _work =>
      sealPre A.ptrBits sch rounds nonce aad aadLen data len tag)
    (post := fun sch rounds nonce aad aadLen data len tag _work =>
      sealPost A.ptrBits sch rounds nonce aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_siv_open` with `work: *mut [u64; n]`. -/
def openScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array false .u8 16), ("work", .array true .u64 n)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (openScratchSig n).contract A
    (pre := fun sch rounds nonce aad aadLen data len tag _work =>
      openPre A.ptrBits sch rounds nonce aad aadLen data len tag)
    (post := fun sch rounds nonce aad aadLen data len tag _work =>
      openPost A.ptrBits sch rounds nonce aad aadLen data len tag)
    (writeArgs := true) (stack := stack)
    (leak := some fun sch rounds nonce aad aadLen data len tag _work =>
      openLeak A.ptrBits sch rounds nonce aad aadLen data len tag)

/-! ## Locality -/

/-- The cipher of a key schedule, for at most 14 rounds, is in its 240 bytes. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 14)
    (h : ∀ i < 240, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p nr = ctxCiph m₁ p nr := by
  simp only [ctxCiph]
  rw [bytesAt_congr fun i hi => h i (by omega)]

theorem le14 {n : Nat} (h : n = 10 ∨ n = 14) : n ≤ 14 := by omega

variable (pb : Nat)

theorem sealPre_local : ∀ vs m₁ m₂, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPre pb) vs m₁ →
      Curry.apply (sealSig.words pb) (sealPre pb) vs m₂
  | [_, _, _, _, _, _, _, _], _, _, _, _, h => h

/-- The inputs of `encryptWith` and `decryptWith` on the memory `m₂` are those
on `m₁` where they agree on the buffers. -/
private theorem inputs_local {pb : Nat} {m₁ m₂ : Mem}
    {sch nonce aad data tag : Addr} {rd al len : BitVec 64}
    (hn : (rd.setWidth pb).toNat ≤ 14)
    (hc : ∀ i < 240 * 1, m₂ (sch + BitVec.ofNat 64 i) = m₁ (sch + BitVec.ofNat 64 i))
    (hN : ∀ i < 12 * 1, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (hA : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hD : ∀ i < len.toNat, m₂ (data + BitVec.ofNat 64 i) = m₁ (data + BitVec.ofNat 64 i))
    (hT : ∀ i < 16 * 1, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    ctxCiph m₂ sch (rd.setWidth pb).toNat = ctxCiph m₁ sch (rd.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ nonce 12 = Spec.Aes.bytesAt m₁ nonce 12 ∧
      Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat = Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ data (len.setWidth pb).toNat = Spec.Aes.bytesAt m₁ data (len.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ tag 16 = Spec.Aes.bytesAt m₁ tag 16 := by
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  simp only [BitVec.toNat_setWidth] at hn ⊢
  exact ⟨ctxCiph_congr hn fun i hi => hc i (by omega), bytesAt_congr fun i hi => hN i (by omega),
    bytesAt_congr fun i hi => hA i (by omega), bytesAt_congr fun i hi => hD i (by omega),
    bytesAt_congr fun i hi => hT i (by omega)⟩

theorem sealPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealSig.words pb) (sealPost pb) vs m₂ m' r
  | [sch, rd, nonce, aad, al, data, len, tag], m₁, m₂, m', r, _, hb, h => by
    simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₂ m' r
    dsimp only [Curry.apply, sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, e₂, e₃, e₄, -⟩ := inputs_local (pb := pb) (tag := tag) (le14 hr)
      (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
      (agree_of hb.2.2.2.2)
    rw [e₁, e₂, e₃, e₄]
    exact h hr

theorem openPre_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPre pb) vs m₁ →
      Curry.apply (openSig.words pb) (openPre pb) vs m₂
  | [_, _, _, _, _, _, _, _], _, _, _, _, h => h

theorem openPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openSig.words pb) (openPost pb) vs m₂ m' r
  | [sch, rd, nonce, aad, al, data, len, tag], m₁, m₂, m', r, _, hb, h => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr] (openPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr] (openPost pb) _ m₂ m' r
    dsimp only [Curry.apply, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := inputs_local (pb := pb) (le14 hr)
      (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
      (agree_of hb.2.2.2.2)
    rw [e₁, e₂, e₃, e₄, e₅]
    exact h hr

theorem openLeak_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openSig.words pb) (openLeak pb) vs m₂
  | [sch, rd, nonce, aad, al, data, len, tag], m₁, m₂, _, hb => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr, ArgWord.int pb, ArgWord.addr] (openLeak pb) _ m₁ =
      Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb,
        ArgWord.addr, ArgWord.int pb, ArgWord.addr] (openLeak pb) _ m₂
    dsimp only [Curry.apply, openLeak, ArgWord.ofRaw, IntTy.bits]
    by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 14
    · simp only [hr, not_true_eq_false, ↓reduceIte]
      obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := inputs_local (pb := pb) (le14 hr)
        (fun i hi => (agree_of hb.1 i hi).symm) (fun i hi => (agree_of hb.2.1 i hi).symm)
        (fun i hi => (agree_of hb.2.2.1 i hi).symm) (fun i hi => (agree_of hb.2.2.2.1 i hi).symm)
        (fun i hi => (agree_of hb.2.2.2.2 i hi).symm)
      simp only [e₁, e₂, e₃, e₄, e₅]
      rfl
    · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcmSiv
