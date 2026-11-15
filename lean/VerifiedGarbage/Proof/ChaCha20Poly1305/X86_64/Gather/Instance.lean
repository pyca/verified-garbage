module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.By
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.FnCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.CT

/-! ### `ChaCha20Poly1305.X86_64.Split.Verified`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.SplitScratch`, which only this module used -/

section

/-!
# `vg_chacha20_poly1305_seal_split` with its working space as an argument

As `seal` (`Scratch.lean`), `vg_chacha20_poly1305_seal_split` keeps its
working space in a frame of its own, around code proved with the working
space as a last argument (`sealSplitScratchContract n`). Its precondition
and postcondition read the memory only within its buffers
(`sealSplitPre_local`, `sealSplitPost_local`, `sealSplitPost_out`): the
precondition reads none, the postcondition the key, the nonce, the
additional data, `src`, the data and the tag.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec.ChaCha20Poly1305

/-- `sealSplitContract`, with `work: *mut [u64; n]` after its arguments,
whatever it holds. -/
def sealSplitScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A sealSplitSig "work" .u64 n (sealSplitPre A.ptrBits) (sealSplitPost A.ptrBits) true stack

variable (pb : Nat)

theorem sealSplitPre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₁ →
      Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem sealSplitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₁ m' r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
    bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := src) (agree_of hb.2.2.2.1),
    bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1)]
  exact h

theorem sealSplitPost_out : ∀ vs m m₁ m₂ r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₁ r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₂ r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2.2)]
  exact h

end VG.Proof.ChaCha20Poly1305

end

end


/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: `Verified`

The contract of `vg_chacha20_poly1305_seal_split` with its working space as
a last argument and the 64 bytes of stack below the stack pointer that its
frame (40) and `seal`'s calls (24) use (`sealSplitScratchContract`) implies
the one the proofs are written against (`splitX86_64`: `FPre`, `splitPost`,
`splitPub`), so the code of the instance calling the implementation `v` of
`vg_chacha20_xor` is `Verified` against it (`sealSplit_verified`), and then,
with its working space in a frame of its own of 1736 bytes (the copies of
`dst`, `len` and `tag` and the address of `work`, and `work`'s 1696 bytes),
against the shared contract with 1800 bytes of stack
(`Verified.stackArgScratchWipedX`, `sealSplit_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-- `vg_chacha20_poly1305_seal_split(key, nonce, aad, aad_len, src, src_len,
dst, len, tag, work)`, as the proofs state it. -/
def splitX86_64 : Contract isa where
  pre := FPre
  post := splitPost
  pub := splitPub

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem fpre_of_spec {s : State} (h : (sealSplitScratchContract X86_64.abi 212 64).pre s) : FPre s := by
  sig_pre [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, sd, st, sw, dt, dw, dg, tw, tg, wg⟩,
    -, -, ra, rs, rdd, rt, rw, -, bk, bn, ba, bs, bd, bt, bw, -, ok, on, oa, os, od, ot, ow, hle⟩ := h
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, sd, st, sw, dt, dw, tw, dg, tg, wg, ra, rs, rdd, rt, rw, bk,
    bn, ba, bs, bd, bt, bw, ok, on, oa, os, od, ot, ow, w₁, w₂, hle⟩

theorem post_of {s s' : State} (h : splitPost s s') : (sealSplitScratchContract X86_64.abi 212 64).post s s' := by
  sig_post [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPost, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq]
  exact fun _ => h

theorem pub_of {s₁ s₂ : State} (hp : (sealSplitScratchContract X86_64.abi 212 64).pub s₁ s₂) : splitPub s₁ s₂ := by
  sig_pub [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨qsp, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃⟩

/-- A state satisfying the precondition, with its working space: no
additional data or data, `dst` at `0x3000`, `tag` at `0x4000` and `work`
at 0, on the stack at `0x8008`. -/
def splitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x1100 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8009 then 0x30 else bif Nat.beq a.toNat 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0, 1696⟩]

theorem splitSat_pre : ∃ s, (sealSplitScratchContract X86_64.abi 212 64).pre s := by
  refine ⟨splitSat, ?_⟩
  sig_pre [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch,
    Proof.ChaCha20Poly1305.sealSplitSig, Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs,
    stackArgs_four, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

theorem split_implies : splitX86_64.Implies (sealSplitScratchContract X86_64.abi 212 64) :=
  ⟨fun _ h => fpre_of_spec h, fun _ _ _ h => post_of h, fun _ _ _ _ h => pub_of h, splitSat_pre⟩

theorem sealSplit_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (sealSplitFor v.callee v.poly) (sealSplitScratchContract X86_64.abi 212 64) :=
  Verified.of_correct (k := splitX86_64) (fun _ hs => let ⟨t, s', e, a, p⟩ := sealSplit_wp v hs; ⟨t, s', e, a, p⟩)
    (sealSplit_ct v) split_implies

/-! ## The frame -/

theorem head_spSafe (whole : Bool) (w : Width) :
    (head whole w).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases whole <;> cases w <;> decide +kernel

theorem head_xdepth (whole : Bool) (w : Width) : (head whole w).x86_64Depth = 0 := by
  cases whole <;> cases w <;> decide +kernel

theorem framed_spSafe {c : Prog isa} (h : c.all (fun i => !X86_64.isa.writesSp i) = true) :
    (framed c).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [framed, Code.all, h, Bool.and_true]; decide

theorem framed_xdepth (c : Prog isa) : (framed c).x86_64Depth = c.x86_64Depth + 40 := by
  simp only [framed, Code.x86_64Depth, X86_64.Instr.frameBytes, Nat.zero_max]; rfl

theorem sealSplitFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealSplitFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealFor_spSafe v
  cases hb : v.poly with
  | avx512 => exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe (sealSplitBody_spSafe v _ (.inl rfl))⟩
  | ifma => exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe (sealSplitBody_spSafe v _ (.inr rfl))⟩
  | scalar => rw [hb] at h₁; exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe h₁⟩
  | avx2 => rw [hb] at h₁; exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe h₁⟩

theorem sealSplitFor_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : (sealSplitFor v.callee v.poly).x86_64Depth ≤ 64 := by
  have h₁ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealFor_xdepth v
  cases hb : v.poly with
  | avx512 => have := sealSplitBody_xdepth v .avx512
              simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [this]
  | ifma => have := sealSplitBody_xdepth v .ifma
            simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [this]
  | scalar => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [h₁]
  | avx2 => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [h₁]

/-- A state satisfying the shared contract's precondition, without the
working space. -/
def splitFrameSat : State :=
  { splitSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩],
                  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩] }

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem splitFrameSat_pre : ∃ s, (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s := by
  refine ⟨splitFrameSat, ?_⟩
  sig_pre [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- `vg_chacha20_poly1305_seal_split` of the instance calling the
implementation `v` of `vg_chacha20_xor`, with its working space in a frame
of its own. -/
theorem sealSplit_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42 (sealSplitFor v.callee v.poly))
      (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Proof.ChaCha20Poly1305.sealSplitSig) (nm := "work") (e := .u64)
    (n := 212) (pre := Proof.ChaCha20Poly1305.sealSplitPre X86_64.abi.ptrBits)
    (post := Proof.ChaCha20Poly1305.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 64)
    (bytes := 1736) (k := 42) (sealSplit_verified v) (by decide) (by decide) (by decide)
    (sealSplitFor_spSafe v) (sealSplitFor_xdepth v) (by decide) (sealSplitPre_local _) (sealSplitPost_local _)
    (sealSplitPost_out _) splitFrameSat_pre

end VG.Proof.ChaCha20Poly1305.X86_64.Split

end

end

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.Verified`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instance it calls

Untrusted: everything here is checked by Lean. For the code of
`vg_chacha20_poly1305_seal_gather` that calls an instance of
`vg_chacha20_poly1305_seal` (`sealGatherWhole`): that instance (`sealFn`),
how many bytes at a time the code copies (`width`), and that only its
frames' pushes and pops write `rsp` (`sealGather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal` calling the implementation
`v` of `vg_chacha20_xor`, with its working space in a frame of its own: its
code as it is without the clearing after it, `…_core`, for the instances
whose `seal` is followed by one (`Scrub.sealReg`), as `seal_gather` clears
its own stack. -/
def sealFn (v : XorImpl) : SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix ++ (if v.poly = .scalar then "_core" else "")
  code := Impl.ChaCha20Poly1305.X86_64.Shared.sealCode v.callee v.poly
  verified := Shared.seal_verified v
  sp := SpSafe.of_all (Shared.seal_sp v)
  depth := Shared.seal_depth v
  E _ _ := True
  exec s h := let ⟨t, s', e, a, p⟩ := (Shared.seal_verified v).1 s h; ⟨t, s', e, a, p, trivial⟩

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGatherWhole (width v) (sealFn v).name (sealFn v).code).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    Shared.seal_sp v
  simp only [sealGatherWhole, Code.all, hc, Bool.and_true, Bool.true_and]
  cases width v <;> decide +kernel

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end


/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instances

Untrusted: everything here is checked by Lean. The instance of
`vg_chacha20_poly1305_seal_gather` for an implementation of
`vg_chacha20_xor` copies as many bytes at a time as its CPUs can (`width`).
With the AVX-512 implementations of `vg_poly1305_blocks`, it calls that
implementation's `vg_chacha20_poly1305_seal` (`Whole.sealFn`) for at most
960 bytes of data (1024 without IFMA, `byLim`), and its `vg_chacha20_poly1305_seal_split` (`sealSplitFn`)
for more (`sealGatherBy`). The others always gather every slice and call
`seal` (`sealGatherWhole`): their `seal_split` would copy the first slice
too (`gatherCode`, `gather_verified`). The code writes `rsp` only in frames
(`gather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal_split` calling the
implementation `v` of `vg_chacha20_xor`, with its working space in a frame
of its own. -/
def sealSplitFn (v : XorImpl) : SealSplitFn where
  name := "vg_chacha20_poly1305_seal_split" ++ v.suffix
  code := withStackArgScratchWipedX 1736 3 42
    (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
  verified := Split.sealSplit_framed v
  sp := SpSafe.of_all (X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v))
  depth := by
    have := Split.sealSplitFor_xdepth v
    simp only [withStackArgScratchWipedX, withStackArgScratch, Code.x86_64Depth, X86_64.Instr.frameBytes,
      Nat.zero_max, Nat.max_zero, Nat.max_le]
    omega_using [this]

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal_split` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGather (width v) (sealSplitFn v).name (sealSplitFn v).code).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealSplitFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
  simp only [sealGather, Code.all, hc, Bool.and_true]
  cases width v <;> decide +kernel

open VG.Proof.ChaCha20.X86_64 in
/-- The code of the instance for `v`. -/
def gatherCode (v : XorImpl) : Prog isa :=
  match v.poly with
  | .avx512 | .ifma => sealGatherBy (byLim v.poly) (width v) (Whole.sealFn v).name (Whole.sealFn v).code (sealSplitFn v).name
      (sealSplitFn v).code
  | _ => sealGatherWhole (width v) (Whole.sealFn v).name (Whole.sealFn v).code

open VG.Proof.ChaCha20.X86_64 in
theorem byLim_cases (v : XorImpl) : byLim v.poly = 961 ∨ byLim v.poly = 1025 := by
  generalize v.poly = b
  cases b <;> decide

open VG.Proof.ChaCha20.X86_64 in
theorem gather_verified (v : XorImpl) :
    Verified X86_64.target (gatherCode v) (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) := by
  unfold gatherCode
  split
  all_goals first
    | exact sealGatherBy_verified (byLim_cases v) _ _ _
    | exact sealGatherWhole_verified _ _

open VG.Proof.ChaCha20.X86_64 in
theorem gather_spSafe (v : XorImpl) : (gatherCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hw := Whole.sealGather_spSafe v
  have hs := sealGather_spSafe v
  unfold gatherCode
  split
  all_goals first
    | exact hw
    | (simp only [sealGatherBy, Code.all, Bool.and_eq_true]
       exact ⟨by rcases byLim_cases v with h | h <;> rw [h] <;> decide, hw, hs⟩)

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
