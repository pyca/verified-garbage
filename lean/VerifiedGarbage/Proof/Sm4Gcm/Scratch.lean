module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SM4-GCM with its working space as an argument

The functions of SM4-GCM keep their working space in a frame of their own
(`Verified.stackScratch`, `Verified.stackArgScratch`), around code proved
with the working space as an argument: `initScratchContract`, … are the
shared contracts of `Spec/Sm4/Gcm/Contract.lean` with a 2560-byte `scratch`
or `work` buffer appended, whatever it holds (`Sig.scratchContract`,
`initScratchContract_eq`, …). `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad` are AES-GCM's (`Proof/AesGcm/Scratch.lean`).

On x86-64 the frames of the functions with an argument on the stack also
hold a copy of the arguments there, which needs the postconditions (and the
leak of `open`) to read the memory on entry only within the function's
buffers (`streamEncryptPost_local`, …): the nonce, the additional data, the
data, the tag, the key context's schedule (`ctxCiph_congr`) and hash subkey
(AES-GCM's `ctxH_congr`), and the streaming state, through `StreamRepr`,
which reads only the state's 80 bytes (AES-GCM's `streamRepr_congr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm

open VG.Spec.Sm4.Gcm
open VG.Proof.AesGcm (bytesAt_congr ctxH_congr streamRepr_congr agree_of)

/-- `vg_sm4_gcm_init` with `scratch: *mut [u64; 320]`. -/
def initScratchSig : Sig where
  params := [("key", .array false .u8 16), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 320)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (post := fun key ctx _scratch => initPost A.ptrBits key ctx)
    (writeArgs := true) (stack := stack)

theorem initScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    initScratchContract A stack = Sig.scratchContract A initSig "scratch" .u64 320
      (Curry.const (fun _ => True) _) (initPost A.ptrBits) true stack := rfl

/-- `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` with
`scratch: *mut [u64; 320]`. -/
def streamCryptScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len"), ("scratch", .array true .u64 320)]

/-- `streamEncryptContract`, whatever `scratch` is. -/
def streamEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

theorem streamEncryptScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    streamEncryptScratchContract A stack = Sig.scratchContract A streamCryptSig "scratch" .u64 320
      (Curry.const (fun _ => True) _) (streamEncryptPost A.ptrBits) true stack := rfl

/-- `streamDecryptContract`, whatever `scratch` is. -/
def streamDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

theorem streamDecryptScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    streamDecryptScratchContract A stack = Sig.scratchContract A streamCryptSig "scratch" .u64 320
      (Curry.const (fun _ => True) _) (streamDecryptPost A.ptrBits) true stack := rfl

/-- `vg_sm4_gcm_stream_finish` with `work: *mut [u64; 320]`. -/
def streamFinishScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("text_len", .int .u64 true), ("tag", .array true .u8 16),
    ("work", .array true .u64 320)]

/-- `streamFinishContract`, whatever `work` is. -/
def streamFinishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishScratchSig.contract A
    (post := fun ctx state aadLen textLen tag _work =>
      streamFinishPost A.ptrBits ctx state aadLen textLen tag)
    (writeArgs := true) (stack := stack)

theorem streamFinishScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    streamFinishScratchContract A stack = Sig.scratchContract A streamFinishSig "work" .u64 320
      (Curry.const (fun _ => True) _) (streamFinishPost A.ptrBits) true stack := rfl

/-- `vg_sm4_gcm_stream_verify` with `work: *mut [u64; 320]`. -/
def streamVerifyScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 320)]
  ret := some .u32

/-- `streamVerifyContract`, whatever `work` is. -/
def streamVerifyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyScratchSig.contract A
    (post := fun ctx state aadLen textLen tag tagLen _work =>
      streamVerifyPost A.ptrBits ctx state aadLen textLen tag tagLen)
    (writeArgs := true) (stack := stack)

theorem streamVerifyScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    streamVerifyScratchContract A stack = Sig.scratchContract A streamVerifySig "work" .u64 320
      (Curry.const (fun _ => True) _) (streamVerifyPost A.ptrBits) true stack := rfl

/-- `vg_sm4_gcm_seal` with `work: *mut [u64; 320]`. -/
def sealScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("nonce", .slice false .u8 "nonce_len"),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("work", .array true .u64 320)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

theorem sealScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    sealScratchContract A stack = Sig.scratchContract A sealSig "work" .u64 320
      (Curry.const (fun _ => True) _) (sealPost A.ptrBits) true stack := rfl

/-- `vg_sm4_gcm_open` with `work: *mut [u64; 320]`. -/
def openScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("nonce", .slice false .u8 "nonce_len"),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 320)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)

theorem openScratchContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    openScratchContract A stack = Sig.scratchContract A openSig "work" .u64 320
      (Curry.const (fun _ => True) _) (openPost A.ptrBits) true stack
      (some (openLeak A.ptrBits)) := rfl

/-! ## Locality -/

/-- The cipher of a key context is in its first 128 bytes, its schedule. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p = ctxCiph m₁ p := by
  simp only [ctxCiph]
  rw [Proof.Sm4.scheduleAt_congr fun k hk => h k (by omega)]

variable (pb : Nat)

/-- A precondition that holds of every memory. -/
theorem pre_local (sig : Sig) : ∀ vs (m₁ m₂ : Mem), vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words pb) (Curry.const (fun _ => True) _) vs m₁ →
      Curry.apply (sig.words pb) (Curry.const (fun _ => True) _) vs m₂ := by
  intro vs _ _ _ _ _
  rw [Curry.apply_const]
  trivial

theorem streamEncryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (streamEncryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptSig.words pb) (streamEncryptPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hs := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamEncryptPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamEncryptPost pb) _ m₂ m' r
  dsimp only [Curry.apply, streamEncryptPost, ArgWord.ofRaw] at h ⊢
  intro iv a p hr hl ht
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
  exact h iv a p (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

theorem streamDecryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (streamDecryptPost pb) vs m₁ m' r →
      Curry.apply (streamCryptSig.words pb) (streamDecryptPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hs := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamDecryptPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamDecryptPost pb) _ m₂ m' r
  dsimp only [Curry.apply, streamDecryptPost, ArgWord.ofRaw] at h ⊢
  intro iv a c hr hl ht
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
  exact h iv a c (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

theorem streamVerifyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamVerifySig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifySig.words pb) (streamVerifyPost pb) vs m₁ m' r →
      Curry.apply (streamVerifySig.words pb) (streamVerifyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamVerifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hs := agree_of hb.2.1
  have ht := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamVerifyPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamVerifyPost pb) _ m₂ m' r
  dsimp only [Curry.apply, streamVerifyPost, ArgWord.ofRaw] at h ⊢
  intro iv a c hr hl hc'
  have := Nat.mod_le tl.toNat (2 ^ pb)
  have e₁ := ctxCiph_congr fun i hi => hc i (by omega)
  have e₂ := ctxH_congr fun i hi => hc i (by omega)
  have e₃ := bytesAt_congr (p := tag) (n := (tl.setWidth pb).toNat) fun i hi => ht i (by
    rw [BitVec.toNat_setWidth] at hi; omega)
  simp only [e₁, e₂, e₃]
  rw [e₁, e₂] at hr
  exact h iv a c (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl hc'

theorem sealPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealSig.words pb) (sealPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hn := agree_of hb.2.1
  have ha := agree_of hb.2.2.1
  have hd := agree_of hb.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (n := (al.setWidth pb).toNat) fun i hi => ha i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

/-- `openResult` on the memory `m₂` is that on `m₁` where they agree on the
buffers. -/
theorem openResult_local {pb : Nat} {m₁ m₂ : Mem}
    {ctx nonce aad data tag : Addr} {nl al len tl : BitVec 64}
    (hc : ∀ i < 32 * 8, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hN : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (hA : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hD : ∀ i < len.toNat, m₂ (data + BitVec.ofNat 64 i) = m₁ (data + BitVec.ofNat 64 i))
    (hT : ∀ i < tl.toNat, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    Spec.Gcm.openResult (ctxCiph m₂ ctx) (Spec.Gcm.ctxH m₂ ctx) (tl.setWidth pb).toNat
        (Spec.Aes.bytesAt m₂ nonce (nl.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₂ data (len.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₂ aad (al.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₂ tag (tl.setWidth pb).toNat) =
      Spec.Gcm.openResult (ctxCiph m₁ ctx) (Spec.Gcm.ctxH m₁ ctx) (tl.setWidth pb).toNat
        (Spec.Aes.bytesAt m₁ nonce (nl.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₁ data (len.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₁ aad (al.setWidth pb).toNat)
        (Spec.Aes.bytesAt m₁ tag (tl.setWidth pb).toNat) := by
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  have := Nat.mod_le tl.toNat (2 ^ pb)
  simp only [BitVec.toNat_setWidth]
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr fun i hi => hN i (by omega), bytesAt_congr fun i hi => hA i (by omega),
    bytesAt_congr fun i hi => hD i (by omega), bytesAt_congr fun i hi => hT i (by omega)]

theorem openPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openSig.words pb) (openPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hN := agree_of hb.2.1
  have hA := agree_of hb.2.2.1
  have hD := agree_of hb.2.2.2.1
  have hT := agree_of hb.2.2.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [openResult_local (pb := pb) hc hN hA hD hT,
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hD i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

theorem openLeak_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openSig.words pb) (openLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _
    m₁ =
    Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _ m₂
  dsimp only [Curry.apply, openLeak, ArgWord.ofRaw, IntTy.bits]
  simp only [openResult_local (pb := pb) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2)]
  rfl

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m₁ m' r →
      Curry.apply (initSig.words pb) (initPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hk := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.addr] (initPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr] (initPost pb) _ m₂ m' r
  dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr (n := 16) fun i hi => hk i (by omega)]
  exact h

theorem streamFinishPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs streamFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamFinishSig.words pb) (streamFinishPost pb) vs m₁ m' r →
      Curry.apply (streamFinishSig.words pb) (streamFinishPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hs := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr] (streamFinishPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr] (streamFinishPost pb) _ m₂ m' r
  dsimp only [Curry.apply, streamFinishPost, ArgWord.ofRaw] at h ⊢
  intro iv a c hr hl ht
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)]
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
  exact h iv a c (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

end VG.Proof.Sm4Gcm
