module

-- separate module: what every target's `_bitsliced` functions share, apart from `Scratch.lean`, which every AES-GCM target imports
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Spec.Gcm.Bitsliced
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PostMono
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM with the round keys bitsliced: the contracts the proofs are written against

The `_bitsliced` functions' contracts (`Spec/Gcm/Bitsliced.lean`) are the
plain ones' with the buffer `bk` as a last argument, which their
postconditions ignore and their preconditions require to hold the
bitsliced form of the key context (`CtxSlicedRepr`). As for the plain
functions (`Rounds.lean`, `Scratch.lean`): the postconditions for `rounds`
of 10, 12 or 14 in terms of the key context (`streamEncryptBitslicedRoundsPost`, …),
the Spec's from them (`streamEncryptBitsliced_keyed`, …), and that the
preconditions and postconditions read memory only within the buffers
(`streamTextBitslicedPre_local`, …), the plain functions' lemmas and
`ctxSlicedRepr_congr`, which reads only the context's and the buffer's bytes.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-! ## The contracts -/

/-- `streamEncryptRoundsPost`, which does not depend on `bk`. -/
def streamEncryptBitslicedRoundsPost (pb : Nat) : streamCryptBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen data len _bk => streamEncryptRoundsPost pb ctx rounds state aadLen textLen data len

/-- `streamDecryptRoundsPost`, which does not depend on `bk`. -/
def streamDecryptBitslicedRoundsPost (pb : Nat) : streamCryptBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen data len _bk => streamDecryptRoundsPost pb ctx rounds state aadLen textLen data len

/-- `streamFinishRoundsPost`, which does not depend on `bk`. -/
def streamFinishBitslicedRoundsPost (pb : Nat) : streamFinishBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen tag _bk => streamFinishRoundsPost pb ctx rounds state aadLen textLen tag

/-- `streamVerifyRoundsPost`, which does not depend on `bk`. -/
def streamVerifyBitslicedRoundsPost (pb : Nat) : streamVerifyBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen tag tagLen _bk =>
    streamVerifyRoundsPost pb ctx rounds state aadLen textLen tag tagLen

def streamEncryptBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedSig.contract A (pre := streamTextBitslicedPre A.ptrBits)
    (post := streamEncryptBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

def streamDecryptBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedSig.contract A (pre := streamTextBitslicedPre A.ptrBits)
    (post := streamDecryptBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

def streamFinishBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishBitslicedSig.contract A (pre := streamFinishBitslicedPre A.ptrBits)
    (post := streamFinishBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

def streamVerifyBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyBitslicedSig.contract A (pre := streamVerifyBitslicedPre A.ptrBits)
    (post := streamVerifyBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-! ## With the working space as an argument

As `Scratch.lean`'s: the contracts with a 2560-byte `work` buffer appended,
whatever it holds, for code proved with the working space as an argument. -/

def streamCryptBitslicedScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len"), ("bk", .array false .u64 156), ("work", .array true .u64 320)]

def streamEncryptBitslicedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len bk _work =>
      streamTextBitslicedPre A.ptrBits ctx rounds state aadLen textLen data len bk)
    (post := fun ctx rounds state aadLen textLen data len bk _work =>
      streamEncryptBitslicedRoundsPost A.ptrBits ctx rounds state aadLen textLen data len bk)
    (writeArgs := true) (stack := stack)

def streamDecryptBitslicedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len bk _work =>
      streamTextBitslicedPre A.ptrBits ctx rounds state aadLen textLen data len bk)
    (post := fun ctx rounds state aadLen textLen data len bk _work =>
      streamDecryptBitslicedRoundsPost A.ptrBits ctx rounds state aadLen textLen data len bk)
    (writeArgs := true) (stack := stack)

def streamFinishBitslicedScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("tag", .array true .u8 16), ("bk", .array false .u64 156), ("work", .array true .u64 320)]

def streamFinishBitslicedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishBitslicedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen tag bk _work =>
      streamFinishBitslicedPre A.ptrBits ctx rounds state aadLen textLen tag bk)
    (post := fun ctx rounds state aadLen textLen tag bk _work =>
      streamFinishBitslicedRoundsPost A.ptrBits ctx rounds state aadLen textLen tag bk)
    (writeArgs := true) (stack := stack)

def streamVerifyBitslicedScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("tag", .slice false .u8 "tag_len"), ("bk", .array false .u64 156), ("work", .array true .u64 320)]
  ret := some .u32

def streamVerifyBitslicedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyBitslicedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen tag tagLen bk _work =>
      streamVerifyBitslicedPre A.ptrBits ctx rounds state aadLen textLen tag tagLen bk)
    (post := fun ctx rounds state aadLen textLen tag tagLen bk _work =>
      streamVerifyBitslicedRoundsPost A.ptrBits ctx rounds state aadLen textLen tag tagLen bk)
    (writeArgs := true) (stack := stack)

/-! ## With the key -/

theorem streamEncryptBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.streamEncryptBitslicedContract A stack) :=
  h.post_mono fun ctx rounds st al tl d l _ => streamEncryptPost_imp _ ctx rounds st al tl d l

theorem streamDecryptBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.streamDecryptBitslicedContract A stack) :=
  h.post_mono fun ctx rounds st al tl d l _ => streamDecryptPost_imp _ ctx rounds st al tl d l

theorem streamFinishBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamFinishBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.streamFinishBitslicedContract A stack) :=
  h.post_mono fun ctx rounds st al tl tag _ => streamFinishPost_imp _ ctx rounds st al tl tag

theorem streamVerifyBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamVerifyBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.streamVerifyBitslicedContract A stack) :=
  h.post_mono fun ctx rounds st al tl tag tagLen _ => streamVerifyPost_imp _ ctx rounds st al tl tag tagLen

/-! ## Locality -/

/-- The bitsliced form of a key context reads only the buffer's 1248 bytes and the context's 256. -/
theorem ctxSlicedRepr_congr {m₁ m₂ : Mem} {bk ctx : Addr}
    (hk : ∀ i < 1248, m₂ (bk + BitVec.ofNat 64 i) = m₁ (bk + BitVec.ofNat 64 i))
    (hc : ∀ i < 256, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (h : CtxSlicedRepr m₁ bk ctx) : CtxSlicedRepr m₂ bk ctx := by
  obtain ⟨h1, h2⟩ := h
  have hw : ∀ d, d + 8 ≤ 1248 → m₂.readW (bk + BitVec.ofNat 64 d) 64 = m₁.readW (bk + BitVec.ofNat 64 d) 64 :=
    fun d hd => Mem.readW_congr fun i hi => by
      rw [Offset.add_add]; exact hk _ (by omega_using [hd, hi])
  simp only [CtxSlicedRepr]
  rw [bytesAt_congr (n := 240) fun i hi => hc i (by omega_using [hi]), ctxH_congr hc]
  refine ⟨fun j hj t ht b hb i hi => ?_, fun i hi j hj => ?_⟩
  · rw [Offset.add_add, hw _ (by omega_using [hj, ht]), ← Offset.add_add]
    exact h1 j hj t ht b hb i hi
  · rw [hw _ (by omega_using [hi, hj])]
    exact h2 i hi j hj

/-- Memory that is zero on the buffer and the context holds the bitsliced
form of the context: of a schedule of zeros and a zero hash subkey. -/
theorem ctxSlicedRepr_of_zero {m : Mem} {bk ctx : Addr}
    (hk : ∀ i < 1248, m (bk + BitVec.ofNat 64 i) = 0) (hc : ∀ i < 256, m (ctx + BitVec.ofNat 64 i) = 0) :
    CtxSlicedRepr m bk ctx := by
  refine ctxSlicedRepr_congr (m₁ := fun _ => 0) (fun i hi => hk i hi) (fun i hi => hc i hi) ?_
  have hr0 : ∀ n (a : Addr), Mem.read (fun _ => 0) a n = 0#(8 * n) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      show (Mem.read (fun _ => 0) (a + 1) n ++ (0 : BitVec 8) : BitVec (8 * n + 8)) = _
      rw [ih]
      exact BitVec.eq_of_getLsbD_eq fun i _ => by simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]; split <;> simp <;> exact BitVec.getLsbD_zero
  have hr : ∀ a : Addr, Mem.readW (fun _ => 0) a 64 = 0 := fun a => by
    rw [Mem.readW, hr0]; rfl
  have hb : ∀ p k, (Spec.Aes.bytesAt (fun _ => 0) p k) = List.replicate k 0 := fun p k => by
    rw [Spec.Aes.bytesAt, List.map_const', List.length_range]
  have hH : ctxH (fun _ => 0) ctx = 0 := by
    simp only [ctxH, blockAt]; rw [hb]; decide
  refine ⟨fun j _ t _ b _ i hi => ?_, fun i hi j hj => ?_⟩
  · rw [hr, hb, Spec.Aes.roundKey, List.drop_replicate, List.take_replicate]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp
  · rw [hr, hH]
    revert i j; decide

variable (pb : Nat)

theorem streamTextBitslicedPre_local : ∀ vs m₁ m₂, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamTextBitslicedPre pb) vs m₁ →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamTextBitslicedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 6
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptBitslicedSig, streamCryptSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨h₁, ctxSlicedRepr_congr (agree_of hb.2.2.2) (agree_of hb.1) h₂⟩

theorem streamEncryptBitslicedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedRoundsPost pb) vs m₁ m' r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamEncryptPost_local pb [x0, x1, x2, x3, x4, x5, x6] m₁ m₂ m' r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamDecryptBitslicedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedRoundsPost pb) vs m₁ m' r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamDecryptPost_local pb [x0, x1, x2, x3, x4, x5, x6] m₁ m₂ m' r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamVerifyBitslicedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamVerifyBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifyBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedRoundsPost pb) vs m₁ m' r →
      Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamVerifyPost_local pb [x0, x1, x2, x3, x4, x5, x6] m₁ m₂ m' r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamEncryptBitslicedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedRoundsPost pb) vs m m₁ r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamEncryptPostOut_local pb [x0, x1, x2, x3, x4, x5, x6] m m₁ m₂ r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamDecryptBitslicedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedRoundsPost pb) vs m m₁ r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamDecryptPostOut_local pb [x0, x1, x2, x3, x4, x5, x6] m m₁ m₂ r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamFinishBitslicedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamFinishBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamFinishBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamFinishBitslicedSig.words pb) (streamFinishBitslicedRoundsPost pb) vs m m₁ r →
      Curry.apply (streamFinishBitslicedSig.words pb) (streamFinishBitslicedRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamFinishPostOut_local pb [x0, x1, x2, x3, x4, x5] m m₁ m₂ r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamVerifyBitslicedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamVerifyBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifyBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedRoundsPost pb) vs m m₁ r →
      Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact streamVerifyPostOut_local pb [x0, x1, x2, x3, x4, x5, x6] m m₁ m₂ r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem streamVerifyBitslicedPre_local : ∀ vs m₁ m₂, vs.length = (streamVerifyBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifyBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedPre pb) vs m₁ →
      Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨streamVerifyPre_local pb [x0, x1, x2, x3, x4, x5, x6] m₁ m₂ rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h₁, ?_⟩
  simp only [streamVerifyBitslicedSig, streamVerifySig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  exact ctxSlicedRepr_congr (agree_of hb.2.2.2) (agree_of hb.1) h₂

theorem streamEncryptBitslicedPost_out : ∀ vs m m₁ m₂ r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedPost pb) vs m m₁ r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamEncryptBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptBitslicedSig, streamCryptSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamEncryptBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamEncryptBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, streamEncryptBitslicedPost, streamEncryptPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a p hr hl ht
  obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hl ht
  have := Nat.mod_le x6.toNat (2 ^ pb)
  refine ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁, Eq.trans ?_ g₂⟩
  exact bytesAt_congr fun i hi => agree_of hb.2.2.1 i (by
    rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])

theorem streamDecryptBitslicedPost_out : ∀ vs m m₁ m₂ r, vs.length = (streamCryptBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedPost pb) vs m m₁ r →
      Curry.apply (streamCryptBitslicedSig.words pb) (streamDecryptBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptBitslicedSig, streamCryptSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamDecryptBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamDecryptBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, streamDecryptBitslicedPost, streamDecryptPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a p hr hl ht
  obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hl ht
  have := Nat.mod_le x6.toNat (2 ^ pb)
  refine ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁, Eq.trans ?_ g₂⟩
  exact bytesAt_congr fun i hi => agree_of hb.2.2.1 i (by
    rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])

theorem streamFinishBitslicedPost_out : ∀ vs m m₁ m₂ r, vs.length = (streamFinishBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamFinishBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamFinishBitslicedSig.words pb) (streamFinishBitslicedPost pb) vs m m₁ r →
      Curry.apply (streamFinishBitslicedSig.words pb) (streamFinishBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamFinishBitslicedSig, streamFinishSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.addr] (streamFinishBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.addr] (streamFinishBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, streamFinishBitslicedPost, streamFinishPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a c hr hl ht
  refine Eq.trans ?_ (h key hk iv a c hr hl ht)
  exact bytesAt_congr fun i hi => agree_of hb.2.2.1 i (by omega_using [hi])

theorem streamVerifyBitslicedPost_out : ∀ vs m m₁ m₂ r, vs.length = (streamVerifyBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifyBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedPost pb) vs m m₁ r →
      Curry.apply (streamVerifyBitslicedSig.words pb) (streamVerifyBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨x0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x4, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x5, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨x6, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamVerifyBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (streamVerifyBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, streamVerifyBitslicedPost, streamVerifyPost, ArgWord.ofRaw] at h ⊢
  exact h

end VG.Proof.AesGcm
