module

-- separate module: the proofs, which need none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild them

public import VerifiedGarbage.Proof.AesGcm.Flag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flag
public import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract
import VerifiedGarbage.Proof.AesGcm.ScratchTo
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SealCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-GCM x86-64: `seal_gather` on a prepared key context whose powers are present

`vg_aes_gcm_seal_gather_prepared`'s code for when the flag says the powers
are present calls `vg_aes_gcm_seal_prepared` and, through its encryption
out of place, `vg_aes_gcm_stream_encrypt_prepared` by their public names,
whose code tests the flag again: so the code of each on the powers is in one
function. These are the contracts of that code and of the internal functions
it calls, on the 1032-byte prepared key context whose flag word is not 1 and
which holds the powers (`Proof.AesGcm.Flag.FlaggedPowers`), and their proofs
(`CtxMode.flagged`), as `Prepared/*.lean` has them for the 1024-byte one.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Flag

open VG.Spec.Gcm

/-! ## The contracts -/

def streamEncryptToFlaggedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len")]

def streamEncryptToFlaggedPre (pb : Nat) : Curry (streamEncryptToFlaggedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _src len _dst dstLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen = len ∧ FlaggedPowers m ctx

def streamEncryptToFlaggedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToFlaggedSig.contract A (pre := streamEncryptToFlaggedPre A.ptrBits)
    (post := Proof.Gcm.streamEncryptToPost A.ptrBits)
    (writeArgs := true) (stack := stack)

def streamEncryptToFlaggedScratchSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"), ("scratch", .array true .u64 274)]

def streamEncryptToFlaggedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToFlaggedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      streamEncryptToFlaggedPre A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (post := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Proof.Gcm.streamEncryptToPost A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (writeArgs := true) (stack := stack)

def sealSplitFlaggedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "src_len"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

def sealSplitFlaggedPre (pb : Nat) : Curry (sealSplitFlaggedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src srcLen _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcLen.toNat ≤ len.toNat ∧
      FlaggedPowers m ctx

def sealSplitFlaggedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitFlaggedSig.contract A (pre := sealSplitFlaggedPre A.ptrBits)
    (post := Proof.Gcm.sealSplitPost A.ptrBits)
    (writeArgs := true) (stack := stack)

def sealGatherFlaggedPre (pb : Nat) : Curry (sealGatherPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ FlaggedPowers m ctx

def sealGatherFlaggedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherFlaggedPre A.ptrBits)
    (post := AesGcm.sealGatherRoundsPost A.ptrBits)
    (writeArgs := true) (stack := stack)

def sealGatherFlaggedScratchSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("scratch", .array true .u64 23)]

def sealGatherFlaggedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherFlaggedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      sealGatherFlaggedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      AesGcm.sealGatherRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (writeArgs := true) (stack := stack)

/-! ## Their pre- and postconditions read the memory only within the buffers -/

variable (pb : Nat)

theorem streamEncryptToFlaggedPre_local : ∀ vs m₁ m₂,
    vs.length = (streamEncryptToFlaggedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToFlaggedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToFlaggedSig.words pb) (streamEncryptToFlaggedPre pb) vs m₁ →
      Curry.apply (streamEncryptToFlaggedSig.words pb) (streamEncryptToFlaggedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamEncryptToFlaggedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := AesGcm.agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToFlaggedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToFlaggedPre pb) _ m₂
  dsimp only [Curry.apply, streamEncryptToFlaggedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, flaggedPowers_congr hc h.2.2⟩

theorem streamEncryptToFlaggedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamEncryptToFlaggedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToFlaggedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToFlaggedSig.words pb) (Proof.Gcm.streamEncryptToPost pb) vs m₁ m' r →
      Curry.apply (streamEncryptToFlaggedSig.words pb) (Proof.Gcm.streamEncryptToPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamEncryptToFlaggedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := AesGcm.agree_of hb.1
  have hs := AesGcm.agree_of hb.2.1
  have hd := AesGcm.agree_of hb.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (Proof.Gcm.streamEncryptToPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (Proof.Gcm.streamEncryptToPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.Gcm.streamEncryptToPost, ArgWord.ofRaw] at h ⊢
  intro hn iv a p hr hl ht
  have := Nat.mod_le len.toNat (2 ^ pb)
  have hn' := le15 hn
  rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  rw [ctxCiph_congr hn' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
  exact h hn iv a p (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

theorem sealGatherFlaggedPre_local : ∀ vs m₁ m₂, vs.length = (sealGatherPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPreparedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPreparedSig.words pb) (sealGatherFlaggedPre pb) vs m₁ →
      Curry.apply (sealGatherPreparedSig.words pb) (sealGatherFlaggedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb hl h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨cnt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealGatherPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  simp only [sealGatherPreparedSig, Sig.lists, List.append_nil] at hl
  have hc := AesGcm.agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealGatherFlaggedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealGatherFlaggedPre pb) _ m₂
  dsimp only [Curry.apply, sealGatherFlaggedPre, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le cnt.toNat (2 ^ pb)
  rw [AesGcm.gatheredLen_congr_le (by rw [BitVec.toNat_setWidth]; exact this) hl]
  exact ⟨h.1, h.2.1, flaggedPowers_congr hc h.2.2⟩

theorem sealGatherFlaggedPost_local : ∀ vs m₁ m₂ m' r,
    vs.length = (sealGatherPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPreparedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPreparedSig.words pb) (AesGcm.sealGatherRoundsPost pb) vs m₁ m' r →
      Curry.apply (sealGatherPreparedSig.words pb) (AesGcm.sealGatherRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb hl h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨cnt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealGatherPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  simp only [sealGatherPreparedSig, Sig.lists, List.append_nil] at hl
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (AesGcm.sealGatherRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (AesGcm.sealGatherRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, AesGcm.sealGatherRoundsPost, ArgWord.ofRaw] at h ⊢
  exact AesGcm.post_local pb (by decide) (AesGcm.agree_of hb.1) (AesGcm.agree_of hb.2.1) (AesGcm.agree_of hb.2.2.1) hl h

end VG.Proof.AesGcm.Flag

/-! ## The functions `seal_gather` calls -/

namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem encSpecF_pre {s : State} (h : encCallPre CtxMode.flagged s) :
    (Proof.AesGcm.Flag.streamEncryptRoundsContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, Spec.Gcm.PreparedRepr, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  all_goals first
    | with_reducible assumption
    | exact Or.inr a₂₂
    | exact Or.inr a₂₂.2

theorem encSpecF_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Proof.AesGcm.Flag.streamEncryptRoundsContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.streamEncryptRoundsPost] at h
  sig_reduce [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecF_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂)
    (o₁ : CtxMode.flagged.ok s₁.mem (s₁.gpr .rdi)) (o₂ : CtxMode.flagged.ok s₂.mem (s₂.gpr .rdi)) :
    (Proof.AesGcm.Flag.streamEncryptRoundsContract X86_64.abi 2608).pub s₁ s₂ := by
  have f₁ : Spec.Gcm.flagLeak s₁.mem (s₁.gpr .rdi) = 0 := by
    simp only [Spec.Gcm.flagLeak]; exact ite_eq_right_iff.mpr fun h => absurd h o₁.1
  have f₂ : Spec.Gcm.flagLeak s₂.mem (s₂.gpr .rdi) = 0 := by
    simp only [Spec.Gcm.flagLeak]; exact ite_eq_right_iff.mpr fun h => absurd h o₂.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedLeak, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.streamEncryptRoundsContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg, Spec.Gcm.streamCryptPreparedLeak]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals try simp only [f₁, f₂]
  all_goals first | with_reducible assumption | trivial | rfl | (intro r hr; simp at hr)

/-- `vg_aes_gcm_stream_encrypt_prepared` from its contract on the prepared key
context, for one whose powers are present: the flag it may leak is 0 in
every call. -/
def EncFn.ofFlagged (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.Flag.streamEncryptRoundsContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.flagged where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecF_pre h)
    exact ⟨t, s', he, ha, encSpecF_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecF_pre h₁) (encSpecF_pre h₂)
    (encSpecF_pub hq h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

end VG.Proof.AesGcm.X86_64.StreamTo

namespace VG.Proof.AesGcm.X86_64.Gather
open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem sealSpecF_pre {s : State} (h : sealPreK CtxMode.flagged s) :
    (Proof.AesGcm.Flag.sealRoundsContract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  sig_pre [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedPre,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, Spec.Gcm.PreparedRepr, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  all_goals first
    | with_reducible assumption
    | exact Or.inr a₃₂
    | exact Or.inr a₃₂.2

theorem sealSpecF_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.Flag.sealRoundsContract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.sealRoundsPost] at h
  sig_reduce [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpecF_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂)
    (o₁ : CtxMode.flagged.ok s₁.mem (s₁.gpr .rdi)) (o₂ : CtxMode.flagged.ok s₂.mem (s₂.gpr .rdi)) :
    (Proof.AesGcm.Flag.sealRoundsContract X86_64.abi 2624).pub s₁ s₂ := by
  have f₁ : Spec.Gcm.flagLeak s₁.mem (s₁.gpr .rdi) = 0 := by
    simp only [Spec.Gcm.flagLeak]; exact ite_eq_right_iff.mpr fun h => absurd h o₁.1
  have f₂ : Spec.Gcm.flagLeak s₂.mem (s₂.gpr .rdi) = 0 := by
    simp only [Spec.Gcm.flagLeak]; exact ite_eq_right_iff.mpr fun h => absurd h o₂.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedLeak, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.sealRoundsContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg, Spec.Gcm.sealPreparedLeak]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals try simp only [f₁, f₂]
  all_goals first | with_reducible assumption | trivial | rfl | (intro r hr; simp at hr)

/-- `vg_aes_gcm_seal_prepared` from its contract on the prepared key context,
for one whose powers are present: the flag it may leak is 0 in every call. -/
def SealFn.ofFlagged (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.Flag.sealRoundsContract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.flagged where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (sealSpecF_pre h)
    exact ⟨t, s', he, ha, sealSpecF_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (sealSpecF_pre h₁) (sealSpecF_pre h₂)
    (sealSpecF_pub hq h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

theorem splitSpecF_pre {s : State} (h : splitPreK CtxMode.flagged s) :
    (Proof.AesGcm.Flag.sealSplitFlaggedContract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    Proof.AesGcm.Flag.sealSplitFlaggedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    Proof.AesGcm.Flag.sealSplitFlaggedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, Spec.Gcm.PreparedRepr, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
    BitVec.setWidth_eq] at *
  all_goals first
    | with_reducible assumption
    | exact ⟨by assumption, by assumption⟩
    | omega

theorem splitSpecF_post {M : CtxMode} {s s' : State}
    (h : (Proof.AesGcm.Flag.sealSplitFlaggedContract X86_64.abi 2672).post s s') (hR : rounds s) :
    (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    Proof.AesGcm.Flag.sealSplitFlaggedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecF_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.AesGcm.Flag.sealSplitFlaggedContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂⟩ := h
  sig_pub [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.sealSplitFlaggedContract, Proof.AesGcm.Flag.sealSplitFlaggedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_split_prepared` from its contract on a context whose powers are present. -/
def SplitFn.ofFlagged (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.Flag.sealSplitFlaggedContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.flagged :=
  CallFn.ofSpec f hv (fun _ h => splitSpecF_pre h)
    (fun _ _ h h' => splitSpecF_post (M := CtxMode.flagged) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecF_pub h) sp xd mx


theorem toSpecF_pre {s : State} (h : toPre CtxMode.flagged s) :
    (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig,
    Proof.AesGcm.Flag.streamEncryptToFlaggedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig,
    Proof.AesGcm.Flag.streamEncryptToFlaggedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, Spec.Gcm.PreparedRepr, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  all_goals first
    | with_reducible assumption
    | omega
    | exact ⟨by assumption, by assumption⟩
    | exact congrArg (BitVec.setWidth 64) a₂

theorem toSpecF_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig,
    Proof.AesGcm.Flag.streamEncryptToFlaggedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.streamEncryptToPost] at h
  sig_reduce [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpecF_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def ToFn.ofFlagged (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.flagged :=
  CallFn.ofSpec f hv (fun _ h => toSpecF_pre h)
    (fun _ _ h h' => toSpecF_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpecF_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

/-! ## `vg_aes_gcm_encrypt_to_prepared` on a context whose powers are present -/

namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.StreamTo

def streamToSatF : State := { streamToSat with rd := [⟨0x1000, 1032⟩, ⟨0x4000, 0⟩, ⟨0x9008, 32⟩] }

def streamToFrameSatF : State := { streamToFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x4000, 0⟩, ⟨0x9008, 24⟩] }

theorem streamToFlagged_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.flagged).Implies
    (Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract,
      Proof.AesGcm.Flag.streamEncryptToFlaggedScratchSig, Proof.AesGcm.Flag.streamEncryptToFlaggedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          post := by sig_implies_post [Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract,
      Proof.AesGcm.Flag.streamEncryptToFlaggedScratchSig, Proof.AesGcm.Flag.streamEncryptToFlaggedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          pub := by sig_implies_pub [Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract,
      Proof.AesGcm.Flag.streamEncryptToFlaggedScratchSig, Proof.AesGcm.Flag.streamEncryptToFlaggedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.flagged, Proof.AesGcm.Flag.FlaggedPowers, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          sat := ⟨streamToSatF, by
            sig_pre [Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract,
              Proof.AesGcm.Flag.streamEncryptToFlaggedScratchSig, Proof.AesGcm.Flag.streamEncryptToFlaggedPre,
              X86_64.abi, X86_64.argRegs, streamToSatF, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptToFlagged_core (T : BlkToFn CtxMode.flagged) (E : EncFn CtxMode.flagged) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.Flag.streamEncryptToFlaggedScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.flagged) (encrypt_correct T E)
    (encrypt_ct T E) streamToFlagged_implies

theorem streamToFrameSatFlagged_pre : ∃ s, (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.streamEncryptToFlaggedContract, Proof.AesGcm.Flag.streamEncryptToFlaggedSig,
    Proof.AesGcm.Flag.streamEncryptToFlaggedPre, Proof.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatF, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem fun _ _ => rfl

theorem streamEncryptToFlagged_framed (T : BlkToFn CtxMode.flagged) (E : EncFn CtxMode.flagged) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Proof.AesGcm.Flag.streamEncryptToFlaggedContract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratch (sig := Proof.AesGcm.Flag.streamEncryptToFlaggedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Proof.AesGcm.Flag.streamEncryptToFlaggedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToFlagged_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.Flag.streamEncryptToFlaggedPre_local _)
    (Proof.AesGcm.Flag.streamEncryptToFlaggedPost_local _) streamToFrameSatFlagged_pre

end VG.Proof.AesGcm.X86_64.StreamTo

/-! ## `vg_aes_gcm_seal_gather_prepared` on a context whose powers are present -/

namespace VG.Proof.AesGcm.X86_64.Gather
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.SealGather

theorem ctx_lowF {i : Nat} (hi : i < 129 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

def gatherSatF : State :=
  { gatherSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 48⟩] }

def gatherFrameSatF : State :=
  { gatherFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩] }

theorem gatherPreFlagged_of {s : State}
    (h : (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.flagged s := by
  sig_pre [Proof.AesGcm.Flag.sealGatherFlaggedScratchContract, Proof.AesGcm.Flag.sealGatherFlaggedScratchSig,
    Proof.AesGcm.Flag.sealGatherFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, dt, dw, dds, ⟨dl, da⟩, tw, tds, ⟨tl, ta⟩, wds, wl, wa⟩,
    rk, rn, ra, rdd, rt, rw, ⟨rds, ⟨rl, -⟩, bk, bn, ba, bd, bt, bw, bds, bl, -⟩, ok, on, oa, od, ot, ow, ⟨ods, ol⟩,
    hr, hg, hpw⟩ := h
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.flagged]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, hpw⟩

theorem gatherPostFlagged_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.Flag.sealGatherFlaggedScratchContract, Proof.AesGcm.Flag.sealGatherFlaggedScratchSig,
    Proof.AesGcm.sealGatherRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubFlagged_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.Flag.sealGatherFlaggedScratchContract, Proof.AesGcm.Flag.sealGatherFlaggedScratchSig,
    Proof.AesGcm.Flag.sealGatherFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi)⟩

theorem gatherSatFlagged_pre : ∃ s, (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.sealGatherFlaggedScratchContract, Proof.AesGcm.Flag.sealGatherFlaggedScratchSig,
    Proof.AesGcm.Flag.sealGatherFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatF, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem fun _ hi => by simp only [ctx_lowF hi, ite_false]

theorem gatherFlagged_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.flagged).Implies
    (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPreFlagged_of h, fun _ _ _ h => gatherPostFlagged_of h, fun _ _ _ _ h => gatherPubFlagged_of h, gatherSatFlagged_pre⟩

/-- `vg_aes_gcm_seal_gather_prepared`'s code: a TLS record's text sealed by
`Sp` from the entry (`withFront long`), and the others by `sealGather`. -/
theorem sealGatherFlagged_core (Sh : ShortFn CtxMode.flagged) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.flagged) (F : FinFn) (Sp : SplitFn CtxMode.flagged) (long : Bool) :
    Verified X86_64.target
      (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Proof.AesGcm.Flag.sealGatherFlaggedScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.flagged)
    (withFront_correct Sh I A T F Sp long false) (withFront_ct Sh I A T F Sp long) gatherFlagged_implies

theorem gatherFrameSatFlagged_pre : ∃ s, (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract, Spec.Gcm.sealGatherPreparedSig,
    Proof.AesGcm.Flag.sealGatherFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatF, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem fun _ hi => by simp only [ctx_lowF hi, ite_false]

theorem sealGatherFlagged_framed (Sh : ShortFn CtxMode.flagged) (I : InitFn)
    (A : AadFn) (T : ToFn CtxMode.flagged) (F : FinFn) (Sp : SplitFn CtxMode.flagged) (long : Bool) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)))
      (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPreparedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Proof.AesGcm.Flag.sealGatherFlaggedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealGatherRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherFlagged_core Sh I A T F Sp long) (by decide) (by decide) (by decide)
    (withFront_spAll Sh I A T F Sp long) (withFront_xdepth Sh I A T F Sp long)
    (Proof.AesGcm.Flag.sealGatherFlaggedPre_local _) (Proof.AesGcm.Flag.sealGatherFlaggedPost_local _)
    gatherFrameSatFlagged_pre

end VG.Proof.AesGcm.X86_64.Gather

/-! ## By the flag -/

namespace VG.Proof.AesGcm.X86_64.Flag

open VG VG.X86_64

/-- By the flag: `c₁` on a context whose powers are present, `c₂` on the key
context. -/
theorem sealGather_onFlagF {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (AesGcm.Flag.sealGatherFlaggedRoundsContract abi 5128))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.of_onFlagCtx (by decide) h₁
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, hf, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    sealGather_satF

end VG.Proof.AesGcm.X86_64.Flag
