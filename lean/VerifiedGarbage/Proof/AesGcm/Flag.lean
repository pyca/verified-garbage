module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Spec.Gcm.Prepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.ScratchOpenTo
import VerifiedGarbage.Proof.AesGcm.Scratch
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Sig

/-!
# AES-GCM's functions on a prepared key context, with the number of rounds

The contracts of `Spec/Gcm/Prepared.lean`'s functions on a prepared key
context (`PreparedRepr`, whose powers may be absent) in the form of
`Proof/AesGcm/Rounds.lean`, which the proofs target (`*RoundsContract`), and
from them the contracts with the key (`*_keyed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.Flag

open VG.Spec.Gcm

/-! ## Their contracts with the number of rounds -/

def sealRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits) (post := AesGcm.sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealPreparedLeak A.ptrBits))

def openRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits) (post := AesGcm.openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openPreparedLeak A.ptrBits))

def streamEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

def streamDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

def sealGatherRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPreparedPre A.ptrBits)
    (post := AesGcm.sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealGatherPreparedLeak A.ptrBits))

def openToRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToPreparedPre A.ptrBits) (post := AesGcm.openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToPreparedLeak A.ptrBits))

/-! ## Leaking only whether the count is at least `t`

The code of an implementation that tests the count against one threshold `t`
(`onFlag t`) leaks only whether it is at least `t` (`flagBit`), which
`flagLeak` determines for `t` of 16 or 48 (`flagBit_of_flagLeak`): it is
proven against these contracts first (`*RoundsContractB`), and so against
the prepared ones (`*_ofB`). Where the count is at least `t`, what it leaks
of it is the same, 1, in every call, so a caller that knows that calls it as
it would code on the powers alone. -/

/-- Whether the count of the prepared key context at `p` is at least `t`. -/
def flagBit (t : Nat) (m : Mem) (p : Addr) : Nat := if t ≤ powerCount m p then 1 else 0

theorem flagBit_of_flagLeak {t : Nat} (ht : t = 16 ∨ t = 48) {m₁ m₂ : Mem} {p₁ p₂ : Addr}
    (h : flagLeak m₁ p₁ = flagLeak m₂ p₂) : flagBit t m₁ p₁ = flagBit t m₂ p₂ := by
  have hi : t ≤ powerCount m₁ p₁ ↔ t ≤ powerCount m₂ p₂ := by
    simp only [flagLeak] at h
    generalize powerCount m₁ p₁ = a at h ⊢
    generalize powerCount m₂ p₂ = b at h ⊢
    by_cases h48a : 48 ≤ a <;> by_cases h48b : 48 ≤ b <;> by_cases h16a : 16 ≤ a <;>
      by_cases h16b : 16 ≤ b <;> simp only [h48a, h48b, h16a, h16b, ↓reduceIte] at h <;>
      rcases ht with rfl | rfl <;> omega
  simp only [flagBit, hi]

theorem flagBit_of_le {t : Nat} {m : Mem} {p : Addr} (h : t ≤ powerCount m p) : flagBit t m p = 1 := by
  simp only [flagBit, h, ↓reduceIte]

def sealLeakB (t pb : Nat) : Curry (sealPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _nonce _nonceLen _aad _aadLen _data _len _tag m => [flagBit t m ctx]

def openLeakB (t pb : Nat) : Curry (openPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m =>
    flagBit t m ctx :: openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m

def streamCryptLeakB (t pb : Nat) : Curry (streamCryptPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _state _aadLen _textLen _data _len m => [flagBit t m ctx]

def sealRoundsContractB (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits) (post := AesGcm.sealRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealLeakB t A.ptrBits))

def openRoundsContractB (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits) (post := AesGcm.openRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeakB t A.ptrBits))

def streamEncryptRoundsContractB (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamEncryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeakB t A.ptrBits))

def streamDecryptRoundsContractB (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := AesGcm.streamDecryptRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptLeakB t A.ptrBits))

/-! ## With the key -/

theorem seal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealRoundsContract A stack)) : Verified T c (sealPreparedContract A stack) :=
  h.post_mono (AesGcm.sealPost_imp _)

theorem open_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openRoundsContract A stack)) : Verified T c (openPreparedContract A stack) :=
  h.post_mono (AesGcm.openPost_imp _)

theorem streamEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamEncryptRoundsContract A stack)) :
    Verified T c (streamEncryptPreparedContract A stack) :=
  h.post_mono (AesGcm.streamEncryptPost_imp _)

theorem streamDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (streamDecryptRoundsContract A stack)) :
    Verified T c (streamDecryptPreparedContract A stack) :=
  h.post_mono (AesGcm.streamDecryptPost_imp _)

theorem sealGather_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherRoundsContract A stack)) :
    Verified T c (sealGatherPreparedContract A stack) :=
  h.post_mono (AesGcm.sealGatherPost_imp _)

theorem openTo_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToRoundsContract A stack)) : Verified T c (openToPreparedContract A stack) :=
  h.post_mono (AesGcm.openToPost_imp _)


/-! ## `open_to` on a prepared key context whose powers are present

The contract of the code that `vg_aes_gcm_open_to_prepared` of an
implementation reading `t` powers (48 or 16) runs, by the count, when they are
present: on the prepared key context whose count is at least `t`
(`FlaggedPowers t`), it calls `vg_aes_gcm_open_prepared`, which tests the
count again. -/

/-- The prepared key context at `p`, whose count is at least `t`. -/
def FlaggedPowers (t : Nat) (m : Mem) (p : Addr) : Prop :=
  t ≤ (m.readW (p + 1024) 64).toNat ∧ PreparedRepr m p

def openToFlaggedPre (t pb : Nat) : Curry (openToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ FlaggedPowers t m ctx

def openToFlaggedRoundsContract (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToFlaggedPre t A.ptrBits) (post := AesGcm.openToRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (Spec.Gcm.openToLeak A.ptrBits))

/-- `open_to` on the prepared key context with `work: *mut [u64; 320]`. -/
def openToFlaggedScratchSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 320)]
  ret := some .u32

/-- `openToFlaggedRoundsContract`, whatever `work` is. -/
def openToFlaggedScratchContract (t : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToFlaggedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      openToFlaggedPre t A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      AesGcm.openToRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _work =>
      Spec.Gcm.openToLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen)

/-- `FlaggedPowers` depends only on bytes within the context. -/
theorem flaggedPowers_congr {t : Nat} {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 129 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : FlaggedPowers t m₁ p) : FlaggedPowers t m₂ p := by
  have e : m₂.readW (p + BitVec.ofNat 64 1024) 64 = m₁.readW (p + BitVec.ofNat 64 1024) 64 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (1024 + i) (by omega)
  have ec : powerCount m₂ p = powerCount m₁ p := by
    simp only [powerCount]
    rw [show (p + 1024 : Addr) = p + BitVec.ofNat 64 1024 from rfl, e]
  refine ⟨?_, fun h16 => AesGcm.preparedPowers16Repr_congr (fun i hi => h i (by omega)) (hr.2.1 (ec ▸ h16)),
    fun h48 => AesGcm.preparedPowersRepr_congr (fun i hi => h i (by omega)) (hr.2.2 (ec ▸ h48))⟩
  rw [show (p + 1024 : Addr) = p + BitVec.ofNat 64 1024 from rfl, e]
  exact hr.1

/-- The witnesses' contexts, at `0x1000`: none of their first 1024 bytes is the
count's. -/
theorem ctx_ne1024 {i : Nat} (hi : i < 128 * 8) : ¬ ((0x1000 + BitVec.ofNat 64 i : Addr) = 0x1400) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega)] at this
  simp at this
  omega

/-- A context whose first 1024 bytes are zeros has the powers (of the hash
subkey 0), and a count of 48 says so. -/
theorem flaggedPowers_of_zeroMem {t : Nat} (ht : t ≤ 48) {m : Mem} {p : Addr}
    (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0)
    (hc : m.readW (p + 1024) 64 = 48) : FlaggedPowers t m p :=
  ⟨by rw [hc]; exact ht, fun _ => AesGcm.preparedPowers16Repr_of (AesGcm.preparedPowersRepr_of_zeroMem h),
    fun _ => AesGcm.preparedPowersRepr_of_zeroMem h⟩

theorem openToFlaggedPre_local (t pb : Nat) : ∀ vs m₁ m₂, vs.length = (openToPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs openToPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToPreparedSig.words pb) (openToFlaggedPre t pb) vs m₁ →
      Curry.apply (openToPreparedSig.words pb) (openToFlaggedPre t pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := AesGcm.agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToFlaggedPre t pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (openToFlaggedPre t pb) _ m₂
  dsimp only [Curry.apply, openToFlaggedPre, ArgWord.ofRaw, IntTy.bits] at h ⊢
  exact ⟨h.1, h.2.1, flaggedPowers_congr hc h.2.2⟩

theorem openToFlaggedRoundsPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPreparedSig.words pb) (AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToPreparedSig.words pb) (AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
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
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [AesGcm.openToResult_local pb hr (fun i hi => AesGcm.agree_of hb.1 i (by omega)) (AesGcm.agree_of hb.2.1) (AesGcm.agree_of hb.2.2.1) (AesGcm.agree_of hb.2.2.2.1)
    (AesGcm.agree_of hb.2.2.2.2.2)]
  exact h hr

theorem openToFlaggedLeak_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToPreparedSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToPreparedSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
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
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [AesGcm.openToResult_local pb hr (fun i hi => AesGcm.agree_of hb.1 i (by omega)) (AesGcm.agree_of hb.2.1) (AesGcm.agree_of hb.2.2.1) (AesGcm.agree_of hb.2.2.2.1)
      (AesGcm.agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcm.Flag
