import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM's key setup and streaming start with their working space as an argument

`vg_aes_gcm_init`, `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` keep
their working space in a frame of their own (`Verified.stackScratch`,
`Verified.regScratch`), around code proved with the working space as an
argument: `initScratchContract`, `streamInitScratchContract` and
`streamAadScratchContract` are the shared contracts with a 2560-byte
`scratch` buffer appended, whatever it holds.

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the pre- and postconditions to read the memory on entry
only within the function's buffers (`initPost_local`, `streamInitPost_local`,
`streamAadPost_local`): the key, the nonce, the data, the key context's hash
subkey (`ctxH_congr`) and the streaming state, through `StreamRepr`, which
reads only the state's 80 bytes (`streamRepr_congr`).
-/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- `vg_aes_gcm_init` with `scratch: *mut [u64; 320]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 320)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_init` with `scratch: *mut [u64; 320]`. -/
def streamInitScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("nonce", .slice false .u8 "nonce_len"),
    ("state", .array true .u64 10), ("scratch", .array true .u64 320)]

/-- `streamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig.contract A
    (post := fun ctx nonce nonceLen state _scratch =>
      streamInitPost A.ptrBits ctx nonce nonceLen state)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_aad` with `scratch: *mut [u64; 320]`. -/
def streamAadScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 320)]

/-- `streamAadContract`, whatever `scratch` is. -/
def streamAadScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadScratchSig.contract A
    (post := fun ctx state aadLen data len _scratch =>
      streamAadPost A.ptrBits ctx state aadLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` with
`scratch: *mut [u64; 320]`. -/
def streamCryptScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len"), ("scratch", .array true .u64 320)]

/-- `streamEncryptContract`, whatever `scratch` is. -/
def streamEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamTextPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptContract`, whatever `scratch` is. -/
def streamDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamTextPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-! ## Locality -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `bytesAt_congr`, at an offset `d` into the agreeing bytes. -/
private theorem bytesAt_congr_off {m₁ m₂ : Mem} {p : Addr} {d n N : Nat} (hn : d + n ≤ N)
    (h : ∀ i < N, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n :=
  bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

/-- The block at offset `d` into the agreeing bytes. -/
private theorem blockAt_congr_off {m₁ m₂ : Mem} {p : Addr} {d N : Nat} (hn : d + 16 ≤ N)
    (h : ∀ i < N, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blockAt m₂ (p + BitVec.ofNat 64 d) = blockAt m₁ (p + BitVec.ofNat 64 d) := by
  simp only [blockAt]
  rw [bytesAt_congr_off hn h]

/-- The hash subkey of a key context is in its 256 bytes. -/
theorem ctxH_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxH m₂ p = ctxH m₁ p := by
  simp only [ctxH]
  exact blockAt_congr_off (d := 240) (by omega) h

/-- The cipher of a key context, for at most 15 rounds, is in its 256 bytes. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 15)
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p nr = ctxCiph m₁ p nr := by
  simp only [ctxCiph]
  rw [bytesAt_congr fun i hi => h i (by omega)]

/-- The streaming state represents a message by its 80 bytes alone. -/
theorem streamRepr_congr {m₁ m₂ : Mem} {p : Addr} {ciph : Block → Block} {hk : Block}
    {iv a c : List Byte}
    (h : ∀ i < 80, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : StreamRepr m₁ p ciph hk iv a c) : StreamRepr m₂ p ciph hk iv a c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  have hp : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  refine ⟨?_, ?_, ?_, ?_, fun hc => ?_⟩
  · rw [hp, blockAt_congr_off (N := 80) (by omega) h, ← hp]; exact h0
  · rw [show p + 16 = p + BitVec.ofNat 64 16 from rfl, blockAt_congr_off (N := 80) (by omega) h]
    exact h1
  · rw [show p + 32 = p + BitVec.ofNat 64 32 from rfl,
      bytesAt_congr_off (N := 80) (by
        have := Nat.mod_lt (ghashInput a c).length (show 16 > 0 by omega); omega) h]
    exact h2
  · rw [show p + 48 = p + BitVec.ofNat 64 48 from rfl, blockAt_congr_off (N := 80) (by omega) h]
    exact h3
  · rw [show p + 64 = p + BitVec.ofNat 64 64 from rfl, blockAt_congr_off (N := 80) (by omega) h]
    exact h4 hc

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem le15 {n : Nat} (h : n = 10 ∨ n = 12 ∨ n = 14) : n ≤ 15 := by omega

variable (pb : Nat)

theorem initPre_local : ∀ vs m₁ m₂, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPre pb) vs m₁ →
      Curry.apply (initSig.words pb) (initPre pb) vs m₂
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

theorem streamInitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamInitSig.words pb).length →
    (∀ b ∈ Sig.bufs streamInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamInitSig.words pb) (streamInitPost pb) vs m₁ m' r →
      Curry.apply (streamInitSig.words pb) (streamInitPost pb) vs m₂ m' r
  | [ctx, nonce, nl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [streamInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hn := agree_of hb.2.1
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (streamInitPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (streamInitPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamInitPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le nl.toNat (2 ^ pb)
    rw [ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem streamAadPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamAadSig.words pb).length →
    (∀ b ∈ Sig.bufs streamAadSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamAadSig.words pb) (streamAadPost pb) vs m₁ m' r →
      Curry.apply (streamAadSig.words pb) (streamAadPost pb) vs m₂ m' r
  | [ctx, st, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [streamAadSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hs := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (streamAadPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (streamAadPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamAadPost, ArgWord.ofRaw] at h ⊢
    intro ciph iv a hr hl
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    rw [ctxH_congr fun i hi => hc i (by omega)] at hr
    exact h ciph iv a (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl

theorem streamTextPre_local : ∀ vs m₁ m₂, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (streamTextPre pb) vs m₁ →
      Curry.apply (streamCryptSig.words pb) (streamTextPre pb) vs m₂
  | [_, _, _, _, _, _, _], _, _, _, _, h => h

theorem streamEncryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (streamEncryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptSig.words pb) (streamEncryptPost pb) vs m₂ m' r
  | [ctx, rd, st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hs := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamEncryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamEncryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamEncryptPost, ArgWord.ofRaw] at h ⊢
    intro hn iv a p hr hl ht
    have := Nat.mod_le len.toNat (2 ^ pb)
    have hn' := le15 hn
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
    exact h hn iv a p (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

theorem streamDecryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (streamDecryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptSig.words pb) (streamDecryptPost pb) vs m₂ m' r
  | [ctx, rd, st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hs := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamDecryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamDecryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, streamDecryptPost, ArgWord.ofRaw] at h ⊢
    intro hn iv a c hr hl ht
    have := Nat.mod_le len.toNat (2 ^ pb)
    have hn' := le15 hn
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
    exact h hn iv a c (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

end VG.Proof.AesGcm
