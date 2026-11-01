module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.FnCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.SplitScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Contract

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
              simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega
  | ifma => have := sealSplitBody_xdepth v .ifma
            simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega
  | scalar => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega
  | avx2 => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega

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
