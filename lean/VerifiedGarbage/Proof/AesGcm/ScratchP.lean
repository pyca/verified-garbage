import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# AES-GCM's `_precomputed` functions with their working space as an argument

`sealPrecomputedScratchContract`, … are the shared contracts of
`Spec/Gcm/Precomputed.lean` with a `work` or `scratch` buffer of 2560 bytes
appended, whatever it holds, as `Scratch.lean`'s are of the others. Their
pre- and postconditions read the memory on entry only within the function's
buffers: the key context's powers of its hash subkey are in its 1024 bytes
(`powersRepr_congr`).
-/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- `vg_aes_gcm_init_precomputed` with `scratch: *mut [u64; 320]`. -/
def initPrecomputedScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 128),
    ("scratch", .array true .u64 320)]

/-- `initPrecomputedContract`, whatever `scratch` is. -/
def initPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initPrecomputedScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPrecomputedPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_precomputed` with `work: *mut [u64; 320]`. -/
def sealPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16), ("work", .array true .u64 320)]

/-- `sealPrecomputedContract`, whatever `work` is. -/
def sealPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrecomputedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPrecomputedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_precomputed` with `work: *mut [u64; 320]`. -/
def openPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"),
    ("work", .array true .u64 320)]
  ret := some .u32

/-- `openPrecomputedContract`, whatever `work` is. -/
def openPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrecomputedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPrecomputedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `vg_aes_gcm_stream_encrypt_precomputed` and `_decrypt_precomputed` with
`scratch: *mut [u64; 320]`. -/
def streamCryptPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len"), ("scratch", .array true .u64 320)]

/-- `streamEncryptPrecomputedContract`, whatever `scratch` is. -/
def streamEncryptPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamTextPrecomputedPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptPrecomputedContract`, whatever `scratch` is. -/
def streamDecryptPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamTextPrecomputedPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-! ## Locality -/

/-- The powers of a key context's hash subkey are in its 1024 bytes. -/
theorem powersRepr_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 128 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) (hr : PowersRepr m₁ p) :
    PowersRepr m₂ p := by
  intro k hk
  rw [blockAt_congr_off (d := 256 + 16 * k) (N := 128 * 8) (by omega) h,
    ctxH_congr fun i hi => h i (by omega)]
  exact hr k hk

variable (pb : Nat)

theorem sealPrecomputedPre_local : ∀ vs m₁ m₂, vs.length = (sealPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealPrecomputedSig.words pb) (sealPrecomputedPre pb) vs m₁ →
      Curry.apply (sealPrecomputedSig.words pb) (sealPrecomputedPre pb) vs m₂
  | [ctx, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, h => by
    simp only [sealPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrecomputedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrecomputedPre pb) _ m₂
    dsimp only [Curry.apply, sealPrecomputedPre, ArgWord.ofRaw] at h ⊢
    exact ⟨h.1, powersRepr_congr hc h.2⟩

theorem openPrecomputedPre_local : ∀ vs m₁ m₂, vs.length = (openPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs openPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrecomputedSig.words pb) (openPrecomputedPre pb) vs m₁ →
      Curry.apply (openPrecomputedSig.words pb) (openPrecomputedPre pb) vs m₂
  | [ctx, _, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, h => by
    simp only [openPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrecomputedPre pb) _
      m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrecomputedPre pb) _
      m₂
    dsimp only [Curry.apply, openPrecomputedPre, ArgWord.ofRaw] at h ⊢
    exact ⟨h.1, powersRepr_congr hc h.2⟩

theorem streamTextPrecomputedPre_local : ∀ vs m₁ m₂, vs.length = (streamCryptPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptPrecomputedSig.words pb) (streamTextPrecomputedPre pb) vs m₁ →
      Curry.apply (streamCryptPrecomputedSig.words pb) (streamTextPrecomputedPre pb) vs m₂
  | [ctx, _, _, _, _, _, _], m₁, m₂, _, hb, h => by
    simp only [streamCryptPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamTextPrecomputedPre pb) _ m₁ at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
      ArgWord.addr, ArgWord.int pb] (streamTextPrecomputedPre pb) _ m₂
    dsimp only [Curry.apply, streamTextPrecomputedPre, ArgWord.ofRaw] at h ⊢
    exact ⟨h.1, powersRepr_congr hc h.2⟩

theorem sealPrecomputedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealPrecomputedSig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealPrecomputedSig.words pb) (sealPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, data, len, _], m₁, m₂, m', r, _, hb, h => by
    simp only [sealPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hn := agree_of hb.2.1
    have ha := agree_of hb.2.2.1
    have hd := agree_of hb.2.2.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₂ m' r
    dsimp only [Curry.apply, sealPost, ArgWord.ofRaw] at h ⊢
    intro hr
    have hr' := le15 hr
    have := Nat.mod_le nl.toNat (2 ^ pb)
    have := Nat.mod_le al.toNat (2 ^ pb)
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [ctxCiph_congr hr' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
      bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
        rw [BitVec.toNat_setWidth] at hi; omega),
      bytesAt_congr (n := (al.setWidth pb).toNat) fun i hi => ha i (by
        rw [BitVec.toNat_setWidth] at hi; omega),
      bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hd i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hr

theorem openPrecomputedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs openPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrecomputedSig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openPrecomputedSig.words pb) (openPost pb) vs m₂ m' r
  | [ctx, rd, nonce, nl, aad, al, data, len, tag, tl], m₁, m₂, m', r, _, hb, h => by
    simp only [openPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hN := agree_of hb.2.1
    have hA := agree_of hb.2.2.1
    have hD := agree_of hb.2.2.2.1
    have hT := agree_of hb.2.2.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
      m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
      m₂ m' r
    dsimp only [Curry.apply, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [openResult_local (pb := pb) (le15 hr) (fun i hi => hc i (by omega)) hN hA hD hT,
      bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hD i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hr

theorem openPrecomputedLeak_local : ∀ vs m₁ m₂, vs.length = (openPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs openPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrecomputedSig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openPrecomputedSig.words pb) (openLeak pb) vs m₂
  | [ctx, rd, nonce, nl, aad, al, data, len, tag, tl], m₁, m₂, _, hb => by
    simp only [openPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
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
      simp only [openResult_local (pb := pb) (le15 hr) (fun i hi => agree_of hb.1 i (by omega)) (agree_of hb.2.1)
        (agree_of hb.2.2.1) (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2)]
      rfl
    · simp only [hr, not_false_eq_true, ↓reduceIte]

theorem streamEncryptPrecomputedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptPrecomputedSig.words pb) (streamEncryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptPrecomputedSig.words pb) (streamEncryptPost pb) vs m₂ m' r
  | [ctx, rd, st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [streamCryptPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
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

theorem streamDecryptPrecomputedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptPrecomputedSig.words pb) (streamDecryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptPrecomputedSig.words pb) (streamDecryptPost pb) vs m₂ m' r
  | [ctx, rd, st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [streamCryptPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
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
