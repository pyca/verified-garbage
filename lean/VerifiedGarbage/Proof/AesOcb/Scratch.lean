import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch

/-!
# AES-OCB with its working space as an argument

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open` keep their
working space in a frame of their own (`Verified.stackScratch`,
`Verified.stackArgScratch`), around code proved with the working space as a
last argument: `initScratchContract`, `sealScratchContract` and
`openScratchContract` are the shared contracts with a 2560-byte buffer
appended, whatever it holds; `sealWorkContract` and `openWorkContract`,
with a buffer of `words` 8-byte words, for an implementation that needs
another size.

A frame that copies arguments passed on the stack needs the pre- and
postconditions, and `open`'s leak, to read the memory on entry only within
the function's buffers (`sealPost_local`, `openPost_local`,
`openLeak_local`, `initPost_local`): the nonce, the associated data, the data, the tag and,
for `rounds` of 10, 12 or 14, the round keys and `L_*` in the key context's
256 bytes (`ctxCiph_congr`, `ctxInv_congr`, `ctxLstar_congr`).
-/

namespace VG.Proof.AesOcb

open VG.Spec.Ocb
open VG.Proof.AesGcm (bytesAt_congr agree_of)

/-- `vg_aes_ocb_init` with `scratch: *mut [u64; 320]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 320)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_ocb_seal` with `work: *mut [u64; 320]`. -/
def sealScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice true .u8 "tag_len"),
    ("work", .array true .u64 320)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_ocb_open` with `work: *mut [u64; 320]`. -/
def openScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"),
    ("work", .array true .u64 320)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `vg_aes_ocb_seal` with `work: *mut [u64; words]`. -/
def sealWorkSig (words : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice true .u8 "tag_len"),
    ("work", .array true .u64 words)]

/-- `sealContract`, whatever `work` (`words` words) is. -/
def sealWorkContract {M : ISA} (A : Abi M) (words : Nat) (stack : Nat := 0) : Contract M :=
  (sealWorkSig words).contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_ocb_open` with `work: *mut [u64; words]`. -/
def openWorkSig (words : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"),
    ("work", .array true .u64 words)]
  ret := some .u32

/-- `openContract`, whatever `work` (`words` words) is. -/
def openWorkContract {M : ISA} (A : Abi M) (words : Nat) (stack : Nat := 0) : Contract M :=
  (openWorkSig words).contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-! ## Locality -/

/-- The cipher of a key context, for at most 15 rounds, is in its 256 bytes. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 15)
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p nr = ctxCiph m₁ p nr := by
  simp only [ctxCiph]
  rw [bytesAt_congr fun i hi => h i (by omega)]

/-- The inverse cipher of a key context, for at most 15 rounds, is in its 256
bytes. -/
theorem ctxInv_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 15)
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxInv m₂ p nr = ctxInv m₁ p nr := by
  simp only [ctxInv]
  rw [bytesAt_congr fun i hi => h i (by omega)]

/-- `L_*` of a key context is in its 256 bytes. -/
theorem ctxLstar_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxLstar m₂ p = ctxLstar m₁ p := by
  have e : Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 240) 16 = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 240) 16 :=
    bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)
  unfold ctxLstar blockAtMem
  exact congrArg ofBytes e

theorem le15 {n : Nat} (h : n = 10 ∨ n = 12 ∨ n = 14) : n ≤ 15 := by omega

/-- The inputs of `encryptWith` and `decryptWith` on the memory `m₂` are those
on `m₁` where they agree on the buffers. -/
private theorem inputs_local {pb : Nat} {m₁ m₂ : Mem}
    {ctx nonce aad data tag : Addr} {rd nl al len tl : BitVec 64}
    (hn : (rd.setWidth pb).toNat ≤ 15)
    (hc : ∀ i < 32 * 8, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hN : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (hA : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hD : ∀ i < len.toNat, m₂ (data + BitVec.ofNat 64 i) = m₁ (data + BitVec.ofNat 64 i))
    (hT : ∀ i < tl.toNat, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    ctxCiph m₂ ctx (rd.setWidth pb).toNat = ctxCiph m₁ ctx (rd.setWidth pb).toNat ∧
      ctxInv m₂ ctx (rd.setWidth pb).toNat = ctxInv m₁ ctx (rd.setWidth pb).toNat ∧
      ctxLstar m₂ ctx = ctxLstar m₁ ctx ∧
      Spec.Aes.bytesAt m₂ nonce (nl.setWidth pb).toNat = Spec.Aes.bytesAt m₁ nonce (nl.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat = Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ data (len.setWidth pb).toNat = Spec.Aes.bytesAt m₁ data (len.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ tag (tl.setWidth pb).toNat = Spec.Aes.bytesAt m₁ tag (tl.setWidth pb).toNat := by
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  have := Nat.mod_le tl.toNat (2 ^ pb)
  simp only [BitVec.toNat_setWidth] at hn ⊢
  have hc' : ∀ i < 256, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i) := fun i hi => hc i hi
  exact ⟨ctxCiph_congr hn hc', ctxInv_congr hn hc', ctxLstar_congr hc',
    bytesAt_congr fun i hi => hN i (by omega), bytesAt_congr fun i hi => hA i (by omega),
    bytesAt_congr fun i hi => hD i (by omega), bytesAt_congr fun i hi => hT i (by omega)⟩

variable (pb : Nat)

theorem sealPre_local : ∀ vs m₁ m₂, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPre pb) vs m₁ →
      Curry.apply (sealSig.words pb) (sealPre pb) vs m₂
  | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, h => h

theorem sealPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealSig.words pb) (sealPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, data, len, tag, tl], m₁, m₂, m', r, _, hb, h => by
    simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealPost pb) _
      m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealPost pb) _
      m₂ m' r
    dsimp only [Curry.apply, sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, -, e₃, e₄, e₅, e₆, -⟩ := inputs_local (pb := pb) (tag := tag) (tl := tl) (le15 hr)
      (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
      (agree_of hb.2.2.2.2)
    rw [e₁, e₃, e₄, e₅, e₆]
    exact h hr

theorem openPre_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPre pb) vs m₁ →
      Curry.apply (openSig.words pb) (openPre pb) vs m₂
  | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, h => h

theorem openPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openSig.words pb) (openPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, data, len, tag, tl], m₁, m₂, m', r, _, hb, h => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
      m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
      m₂ m' r
    dsimp only [Curry.apply, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := inputs_local (pb := pb) (le15 hr)
      (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
      (agree_of hb.2.2.2.2)
    rw [e₁, e₂, e₃, e₄, e₅, e₆, e₇]
    exact h hr

theorem openLeak_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openSig.words pb) (openLeak pb) vs m₂
  | [ctx, rd, nonce, nl, aad, al, data, len, tag, tl], m₁, m₂, _, hb => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _
      m₁ =
      Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _ m₂
    dsimp only [Curry.apply, openLeak, ArgWord.ofRaw, IntTy.bits]
    by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨
      (rd.setWidth pb).toNat = 14
    · simp only [hr, not_true_eq_false, ↓reduceIte]
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := inputs_local (pb := pb) (le15 hr)
        (fun i hi => (agree_of hb.1 i hi).symm) (fun i hi => (agree_of hb.2.1 i hi).symm)
        (fun i hi => (agree_of hb.2.2.1 i hi).symm) (fun i hi => (agree_of hb.2.2.2.1 i hi).symm)
        (fun i hi => (agree_of hb.2.2.2.2 i hi).symm)
      simp only [e₁, e₂, e₃, e₄, e₅, e₆, e₇]
      rfl
    · simp only [hr, not_false_eq_true, ↓reduceIte]

theorem initPre_local : ∀ vs m₁ m₂, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPre pb) vs m₁ → Curry.apply (initSig.words pb) (initPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m₁ m' r →
      Curry.apply (initSig.words pb) (initPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₂ m' r
    dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

end VG.Proof.AesOcb
