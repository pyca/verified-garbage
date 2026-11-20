module

public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.PostMono

/-! ### `AesOcb.Rounds`, which this module and modules that import it used -/

section

/-!
# AES-OCB: the contracts on the key context and the number of rounds they are given

Not trusted: the contracts that the proofs of `vg_aes_ocb_seal` and `vg_aes_ocb_open` are written against, for
the ciphers of the key context for the number of rounds they are given
(`Spec.Ocb.ctxCiph`, `Spec.Ocb.ctxInv`, `Spec.Ocb.ctxLstar`), whatever key the context came from. The shared contracts in
`Spec/` are stated for every key whose context is in memory with its number
of rounds (`Spec.Ocb.KeyRounds`), and follow from these
(`Verified.post_mono`).
-/

@[expose] public section

namespace VG.Proof.AesOcb

open VG.Spec
open VG.Spec.Ocb

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: the `len`
bytes at `data` are encrypted, with the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`encryptWith`), and the tag of `tag_len`
bytes is at `tag`. -/
def sealRoundsPost (pb : Nat) : sealSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxLstar m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m data len.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag tagLen.toNat)

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx`: encrypts the `len` bytes at `data`
in place, with the nonce at `nonce` and the `aad_len` bytes of associated
data at `aad` (`encryptWith`), and writes the tag of `tag_len` bytes to
`tag`. -/
def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if the tag is right for the `len`
bytes of encrypted data at `data`, the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`decryptWith`), the result is 1 and the
plaintext is at `data`; otherwise the result is 0 and zeros are at
`data`. -/
def openRoundsPost (pb : Nat) : openSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
        (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx` and the received tag the `tag_len`
bytes at `tag`: if the tag is right for the `len` bytes of encrypted data at
`data`, the nonce at `nonce` and the `aad_len` bytes of associated data at
`aad` (`decryptWith`), returns 1 and leaves the plaintext at `data`;
otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openRoundsPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- What the key context of a key holds, with the key's number of rounds:
the key's ciphers and `L_*`, for 10, 12 or 14 rounds. -/
theorem keyRounds_ctx {m : Mem} {ctx : Addr} {r : Nat} {key : List Byte}
    (h : Spec.Ocb.KeyRounds m ctx r key) :
    ctxCiph m ctx r = aes key ∧ ctxInv m ctx r = aesInv key ∧ ctxLstar m ctx = aes key 0 ∧
      (r = 10 ∨ r = 12 ∨ r = 14) := by
  obtain ⟨hl, hr, hk⟩ := h
  subst hr
  refine ⟨by unfold ctxCiph; rw [hk.1]; rfl, by unfold ctxInv; rw [hk.1]; rfl, hk.2, ?_⟩
  rcases hl with h | h | h <;> rw [h] <;> decide

/-- `Spec.Ocb.sealContract` from `sealRoundsContract`. -/
theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (Spec.Ocb.sealContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [sealRoundsPost, Spec.Ocb.sealPost] at hp ⊢
    obtain ⟨hc, hi, hs, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hs] at h'
    exact h'

/-- `Spec.Ocb.openContract` from `openRoundsContract`. -/
theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (Spec.Ocb.openContract A stack) :=
  h.post_mono fun ctx rounds _ _ _ _ _ _ _ _ m _ _ hp key hk => by
    dsimp only [openRoundsPost, Spec.Ocb.openPost] at hp ⊢
    obtain ⟨hc, hi, hs, hg⟩ := keyRounds_ctx hk
    have h' := hp hg
    rw [hc, hi, hs] at h'
    split
    all_goals
      rename_i heq
      rw [heq] at h'
      exact h'

end VG.Proof.AesOcb

end

end

/-!
# AES-OCB with its working space as an argument

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open` keep their
working space in a frame of their own (`Verified.stackScratch`,
`Verified.stackArgScratch`), around code proved with the working space as a
last argument: `initScratchContract`, `sealScratchContract` and
`openScratchContract` are the shared contracts with a buffer appended
(2560 bytes, or `8 n`), whatever it holds; `initWorkContract`, `sealWorkContract` and
`openWorkContract`, with a buffer of `words` 8-byte words, for an
implementation that needs another size.

A frame that copies arguments passed on the stack needs the pre- and
postconditions, and `open`'s leak, to read the memory on entry only within
the function's buffers (`sealPost_local`, `openPost_local`,
`openLeak_local`, `initPost_local`): the nonce, the associated data, the data, the tag and,
for `rounds` of 10, 12 or 14, the round keys and `L_*` in the key context's
256 bytes (`ctxCiph_congr`, `ctxInv_congr`, `ctxLstar_congr`).
-/

@[expose] public section

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

/-- `vg_aes_ocb_init` with `scratch: *mut [u64; 3]`, for the implementations
whose callees need no working space (x86-64's AES-NI and VAES ones). -/
def initScratchSigF : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 3)]

/-- `initContract`, whatever `scratch` is (of 3 words). -/
def initScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigF.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_ocb_seal` with `work: *mut [u64; n]` (320 words but on PPC64LE). -/
def sealScratchSig (n : Nat := 320) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice true .u8 "tag_len"),
    ("work", .array true .u64 n)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) (n : Nat := 320) : Contract M :=
  (sealScratchSig n).contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      sealRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_ocb_open` with `work: *mut [u64; n]` (320 words but on PPC64LE). -/
def openScratchSig (n : Nat := 320) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"),
    ("work", .array true .u64 n)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) (n : Nat := 320) : Contract M :=
  (openScratchSig n).contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `vg_aes_ocb_init` with `scratch: *mut [u64; words]`. -/
def initWorkSig (words : Nat) : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 words)]

/-- `initContract`, whatever `scratch` (`words` words) is. -/
def initWorkContract {M : ISA} (A : Abi M) (words : Nat) (stack : Nat := 0) : Contract M :=
  (initWorkSig words).contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

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
      sealRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
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
      openRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-! ## Locality -/

/-- The cipher of a key context, for at most 15 rounds, is in its 256 bytes. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 15)
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p nr = ctxCiph m₁ p nr := by
  simp only [ctxCiph]
  rw [bytesAt_congr fun i hi => h i (by omega_using [hn, hi])]

/-- The inverse cipher of a key context, for at most 15 rounds, is in its 256
bytes. -/
theorem ctxInv_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 15)
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxInv m₂ p nr = ctxInv m₁ p nr := by
  simp only [ctxInv]
  rw [bytesAt_congr fun i hi => h i (by omega_using [hn, hi])]

/-- `L_*` of a key context is in its 256 bytes. -/
theorem ctxLstar_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 256, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxLstar m₂ p = ctxLstar m₁ p := by
  have e : Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 240) 16 = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 240) 16 :=
    bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega_using [hi])
  unfold ctxLstar blockAtMem
  exact congrArg ofBytes e

theorem le15 {n : Nat} (h : n = 10 ∨ n = 12 ∨ n = 14) : n ≤ 15 := by omega_using [h]

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
    bytesAt_congr fun i hi => hN i (by omega_arith), bytesAt_congr fun i hi => hA i (by omega_arith),
    bytesAt_congr fun i hi => hD i (by omega_arith), bytesAt_congr fun i hi => hT i (by omega_using [this, hi])⟩

variable (pb : Nat)

theorem sealPre_local : ∀ vs m₁ m₂, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPre pb) vs m₁ →
      Curry.apply (sealSig.words pb) (sealPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem sealPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealRoundsPost pb) vs m₁ m' r →
      Curry.apply (sealSig.words pb) (sealRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
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
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealRoundsPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealRoundsPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, sealRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  obtain ⟨e₁, -, e₃, e₄, e₅, e₆, -⟩ := inputs_local (pb := pb) (tag := tag) (tl := tl) (le15 hr)
    (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2)
  rw [e₁, e₃, e₄, e₅, e₆]
  exact h hr

/-- `sealRoundsPost` reads the memory on return only within the buffers. -/
theorem sealPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (sealSig.words pb).length →
    Curry.apply (sealSig.words pb) (sealPre pb) vs m →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealRoundsPost pb) vs m m₁ r →
      Curry.apply (sealSig.words pb) (sealRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen _ hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
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
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealRoundsPost pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (sealRoundsPost pb) _
    m m₂ r
  dsimp only [Curry.apply, sealRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  obtain ⟨-, -, -, -, -, e₆, e₇⟩ := inputs_local (pb := pb) (le15 hr)
    (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2)
  rw [e₆, e₇]
  exact h hr

theorem openPre_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPre pb) vs m₁ →
      Curry.apply (openSig.words pb) (openPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem openPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openRoundsPost pb) vs m₁ m' r →
      Curry.apply (openSig.words pb) (openRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
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
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openRoundsPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openRoundsPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, openRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := inputs_local (pb := pb) (le15 hr)
    (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2)
  rw [e₁, e₂, e₃, e₄, e₅, e₆, e₇]
  exact h hr

/-- `openRoundsPost` reads the memory on return only within the buffers. -/
theorem openPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (openSig.words pb).length →
    Curry.apply (openSig.words pb) (openPre pb) vs m →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openRoundsPost pb) vs m m₁ r →
      Curry.apply (openSig.words pb) (openRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen _ hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
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
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openRoundsPost pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openRoundsPost pb) _
    m m₂ r
  dsimp only [Curry.apply, openRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  obtain ⟨-, -, -, -, -, e₆, -⟩ := inputs_local (pb := pb) (le15 hr)
    (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2)
  rw [e₆]
  exact h hr

theorem openLeak_local : ∀ vs m₁ m₂, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openSig.words pb) (openLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
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
    Curry.apply (initSig.words pb) (initPre pb) vs m₁ → Curry.apply (initSig.words pb) (initPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m₁ m' r →
      Curry.apply (initSig.words pb) (initPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hk := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₂ m' r
  dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le kl.toNat (2 ^ pb)
  rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
    rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])]
  exact h


/-- `initPost` reads the memory on return only within the key context, for a
key of a length the precondition allows. -/
theorem initPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (initSig.words pb).length →
    Curry.apply (initSig.words pb) (initPre pb) vs m →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m m₁ r →
      Curry.apply (initSig.words pb) (initPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hp hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPre pb) _ m at hp
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m m₂ r
  dsimp only [Curry.apply, initPre, initPost, ArgWord.ofRaw] at hp h ⊢
  obtain ⟨h1, h2⟩ := h
  have hn : 16 * (Spec.Aes.rounds ((Spec.Aes.bytesAt m key (kl.setWidth pb).toNat).length / 4) + 1) ≤ 256 := by
    simp only [Spec.Aes.bytesAt, List.length_map, List.length_range]
    rcases hp with e | e | e <;> rw [e] <;> decide
  exact ⟨(bytesAt_congr fun i hi => hc i (by omega_using [hn, hi])).trans h1,
    (ctxLstar_congr fun i hi => hc i hi).trans h2⟩

end VG.Proof.AesOcb
