module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8

/-!
# AES-GCM `open_split_with_powers` on AArch64: the contract

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split_with_powers`
`(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len, pw,
src, src_len) -> u32` (`Impl.AesGcm.AArch64.Stitch.openSplitWithPw`) is
`vg_aes_gcm_open_with_powers` with the ciphertext read from the `len` bytes
at `src` (`src_len` is `len`) and the plaintext written to `dst`, which it
leaves unspecified when the tag is wrong (its caller zeroes it), for a TLS
record: a 12-byte nonce and at most 16 bytes of additional data. Only
verified code calls it (`vg_aes_gcm_open_to_with_powers`), so its contract is
here, with no `Api`: `sig` lays out its arguments as `open_with_powers`'s,
with `src` and its length after `pw`, so `work`, appended by
`Sig.scratchContract`, is the stack argument 5.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.OpenSplit

open VG VG.Spec.Gcm

/-- The arguments of `vg_aes_gcm_open_split_with_powers`. -/
def sig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("dst", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"), ("pw", .array false .u64 16),
    ("src", .slice false .u8 "src_len")]
  ret := some .u32

/-- `rounds` is 10, 12 or 14, `pw` holds the powers of the key context's hash
subkey, `src_len` is `len`, the nonce is 12 bytes long and the additional
data at most 16. -/
def pre (pb : Nat) : Curry (sig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce nonceLen _aad aadLen _dst len _tag _tagLen pw _src srcLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ Powers8Repr m pw (ctxH m ctx) ∧
      srcLen.toNat = len.toNat ∧ nonceLen.toNat = 12 ∧ aadLen.toNat ≤ 16

/-- For `rounds` of 10, 12 or 14: `open`'s result on the ciphertext at `src`
(`openRoundsPost`), the plaintext at `dst` if the tag is right. -/
def post (pb : Nat) : sig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen dst len tag tagLen _pw src srcLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Spec.Aes.bytesAt m nonce nonceLen.toNat) (Spec.Aes.bytesAt m src srcLen.toNat)
        (Spec.Aes.bytesAt m aad aadLen.toNat) (Spec.Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Spec.Aes.bytesAt m' dst len.toNat = pt
    | none => r = 0

/-- What it may leak: whether the tag is right (`openLeak`, of the
ciphertext at `src`). -/
def leak (pb : Nat) : Curry (sig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen _dst _len tag tagLen _pw src srcLen m =>
    if ¬(rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) then [] else
    [if (openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Spec.Aes.bytesAt m nonce nonceLen.toNat) (Spec.Aes.bytesAt m src srcLen.toNat)
        (Spec.Aes.bytesAt m aad aadLen.toNat) (Spec.Aes.bytesAt m tag tagLen.toNat)).isSome
      then 1 else 0]

/-- `vg_aes_gcm_open_split_with_powers`, with `stack` bytes below the stack
pointer. -/
def contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sig.contract A (pre := pre A.ptrBits) (post := post A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (leak A.ptrBits))

/-- Its code before `withStackArgScratch`: the same, with `work` after `src_len`. -/
def scratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A sig "work" .u64 320 (pre A.ptrBits) (post A.ptrBits) true stack (some (leak A.ptrBits))

/-! ## Locality -/

variable (pb : Nat)

theorem pre_local : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words pb) (pre pb) vs m₁ → Curry.apply (sig.words pb) (pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 12) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sig, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := Proof.AesGcm.agree_of hb.1
  have hp := Proof.AesGcm.agree_of hb.2.2.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (pre pb) _ m₂
  dsimp only [Curry.apply, pre, ArgWord.ofRaw] at h ⊢
  rw [Proof.AesGcm.ctxH_congr fun i hi => hc i (by omega)]
  exact ⟨h.1, Proof.AesGcm.powers8Repr_congr hp h.2.1, h.2.2⟩

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words pb) (post pb) vs m₁ m' r → Curry.apply (sig.words pb) (post pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 12) hlen
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
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sig, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (post pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (post pb) _ m₂ m' r
  dsimp only [Curry.apply, post, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [Proof.AesGcm.openResult_local (pb := pb) (Proof.AesGcm.le15 hr)
    (fun i hi => Proof.AesGcm.agree_of hb.1 i (by omega)) (Proof.AesGcm.agree_of hb.2.1)
    (Proof.AesGcm.agree_of hb.2.2.1) (Proof.AesGcm.agree_of hb.2.2.2.2.2.2)
    (Proof.AesGcm.agree_of hb.2.2.2.2.1)]
  exact h hr

theorem leak_local : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words pb) (leak pb) vs m₁ = Curry.apply (sig.words pb) (leak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 12) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sig, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (leak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr,
    ArgWord.int pb] (leak pb) _ m₂
  dsimp only [Curry.apply, leak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨
    (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [Proof.AesGcm.openResult_local (pb := pb) (Proof.AesGcm.le15 hr)
      (fun i hi => Proof.AesGcm.agree_of hb.1 i (by omega)) (Proof.AesGcm.agree_of hb.2.1)
      (Proof.AesGcm.agree_of hb.2.2.1) (Proof.AesGcm.agree_of hb.2.2.2.2.2.2)
      (Proof.AesGcm.agree_of hb.2.2.2.2.1)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcm.AArch64.OpenSplit
