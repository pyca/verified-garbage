module

public import VerifiedGarbage.Proof.HmacTable.RISCV64
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Impl.Hkdf.RISCV64
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Hkdf.RISCV64
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# HKDF on RISC-V: the calls of a table's HMAC functions, and `vg_hkdf_key`, correct

The contract the proof is written against (`keyR`), for the table `hmac` of
one hash function `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold
HMAC's states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming
states). In its frame (`kFr` bytes: `ra` and `s6`), the prologue saves them,
moves the table to `s6` and the arguments of HMAC's `init` into place
(`pro_ok`); `init`, through the table, writes the states (`init_ok`); the
epilogue restores `ra` and `s6`, which nothing else wrote (`epi_ok`).
-/

@[expose] public section

/-! ## The calls of a table's HMAC functions

For a hash function with HMAC on RISC-V (`HVar`): what a call of HMAC's
`init` (`hi_call`), the streaming `update` (`upd_call`) or HMAC's `finalize`
(`hf_call`) needs of the state it is called from (`HiArgs`, `UpdArgs`,
`HfArgs`), against the contracts of their generic proofs, and what holds
when it returns (`After`); that two runs of each with the same arguments
leak the same trace (`hi_rel`, `upd_rel`, `hf_rel`); and the indirect call
of a table's function `j` (`tcall`), at the address the table holds, which
is the function's (`tcall_ok`, `tcall_rel`). Deterministic ECDSA's proofs
(`Proof/Ecdsa/Rfc6979/RISCV64/Common.lean`) have the same, for its frame.
-/

namespace VG.Proof.Hkdf.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_ld)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (tcall)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG updK)
open VG.Proof.HmacTable.RISCV64 (HVar)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

end VG.Proof.Hkdf.RISCV64

namespace VG.Proof.HmacTable.RISCV64.HVar

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)

variable (w : HVar)

/-- What the proofs know of the hash function's code. -/
abbrev hH : HashOK w.H := w.t.l.ok

/-- HMAC's `init`, with its frame and its callees' stack. -/
abbrev hiK : Contract isa := initG w.hH.SH (w.H.ibytes + w.H.F)

/-- HMAC's `finalize`, with its frame and its callees' stack. -/
abbrev hfK : Contract isa := finG w.hH.SH (w.H.fbytes + w.H.F)

theorem hi_sdepth : sdepth w.H.init ≤ w.H.ibytes + w.H.F := by
  have := w.hH.initSd; have := w.hH.updSd; have := w.hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes, Nat.zero_max, Nat.max_zero,
    Nat.max_self, Nat.add_le_add_iff_left, Nat.max_le]
  -- the bound of each call, which `omega` otherwise finds by splitting every `max`
  omega_arith

theorem hf_sdepth : sdepth w.H.finalize ≤ w.H.fbytes + w.H.F := by
  have := w.hH.updSd; have := w.hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega_arith

theorem hi_ok : ∀ s, w.hiK.pre s → ∃ t s', Exec isa w.H.init s t s' ∧ abiPreserved s s' ∧ w.hiK.post s s' :=
  fun _ hs => by
    obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Init.correct w.hH hs
    exact ⟨t, s', he, h₁, h₂⟩

theorem hf_ok : ∀ s, w.hfK.pre s → ∃ t s', Exec isa w.H.finalize s t s' ∧ abiPreserved s s' ∧ w.hfK.post s s' :=
  fun _ hs => by
    obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Finalize.correct w.hH hs
    exact ⟨t, s', he, h₁, h₂⟩

end VG.Proof.HmacTable.RISCV64.HVar

namespace VG.Proof.Hkdf.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_ld)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (tcall)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG updK)
open VG.Proof.HmacTable.RISCV64 (HVar)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## HMAC's `init` -/

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (w : HVar) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a2 : s.gpr .a2 = k
  a3 : (s.gpr .a3).toNat = kl
  al : s.sp.toNat % 16 = 0
  sp : w.H.ibytes + w.H.F ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, w.H.S⟩ ⟨ou, w.H.S⟩
  d_ki : Region.Disjoint ⟨k, kl⟩ ⟨inn, w.H.S⟩
  d_ko : Region.Disjoint ⟨k, kl⟩ ⟨ou, w.H.S⟩
  b_i : (below s.sp (w.H.ibytes + w.H.F)).Disjoint ⟨inn, w.H.S⟩
  b_o : (below s.sp (w.H.ibytes + w.H.F)).Disjoint ⟨ou, w.H.S⟩
  b_k : (below s.sp (w.H.ibytes + w.H.F)).Disjoint ⟨k, kl⟩
  hc : RISCV64.Covers ([⟨k, kl⟩] ++ [⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩] s.wr

section
variable {w : HVar}

theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs w s inn ou k kl) :
    w.hiK.pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, w.hH.SH.stateBytes⟩, ⟨ou, w.hH.SH.stateBytes⟩]) := by
  have hS := w.hH.hS
  simp only [HVar.hiK, initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, hS]
  exact ⟨trivial, trivial, h.d_io, h.d_ki, h.d_ko, h.al, h.sp, h.b_i, h.b_o, h.b_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs w s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩] ++ [below s.sp (w.H.ibytes + w.H.F)]) s' →
      w.hH.SH.Repr s'.mem inn (xorPad (blockKey w.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      w.hH.SH.Repr s'.mem ou (xorPad (blockKey w.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call w.hiN w.H.init) s Q := by
  have hS := w.hH.hS
  have hl := w.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = k := (State.callEntry_gpr _ (by decide)).trans h.a2
  have c3 : (s.callEntry.gpr .a3).toNat = kl := by rw [State.callEntry_gpr _ (by decide), h.a3]
  refine WP.callAny (k := w.hiK) w.hi_ok (rd := [⟨k, kl⟩])
    (wr := [⟨inn, w.hH.SH.stateBytes⟩, ⟨ou, w.hH.SH.stateBytes⟩]) h.pre (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := w.hi_sdepth; have := hl.ibytes; have := hl.F; omega_arith)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [HVar.hiK, initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
    c3] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf w.hi_sdepth (by have := hl.ibytes; have := hl.F; omega_arith)

/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {Q : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', Q s s' → HiArgs w s inn ou k kl ∧ HiArgs w s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa Q (.call w.hiN w.H.init) fun _ _ => True := by
  have hS := w.hH.hS
  refine RelCT.call w.hi_ok w.hiCt [⟨k, kl⟩] [⟨inn, w.hH.SH.stateBytes⟩, ⟨ou, w.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  simp only [HVar.hiK, initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

end

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou` and `out` at `o`. -/
structure HfArgs (w : HVar) (s : State) (inn ou o : Addr) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a3 : s.gpr .a3 = o
  al : s.sp.toNat % 16 = 0
  sp : w.H.fbytes + w.H.F ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, w.H.S⟩ ⟨ou, w.H.S⟩
  d_io : Region.Disjoint ⟨inn, w.H.S⟩ ⟨o, w.H.D⟩
  d_uo : Region.Disjoint ⟨ou, w.H.S⟩ ⟨o, w.H.D⟩
  b_i : (below s.sp (w.H.fbytes + w.H.F)).Disjoint ⟨inn, w.H.S⟩
  b_u : (below s.sp (w.H.fbytes + w.H.F)).Disjoint ⟨ou, w.H.S⟩
  b_o : (below s.sp (w.H.fbytes + w.H.F)).Disjoint ⟨o, w.H.D⟩
  hc : RISCV64.Covers ([⟨ou, w.H.S⟩] ++ [⟨inn, w.H.S⟩, ⟨o, w.H.D⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, w.H.S⟩, ⟨o, w.H.D⟩] s.wr

section
variable {w : HVar}

theorem HfArgs.pre {s : State} {inn ou o : Addr} (h : HfArgs w s inn ou o) :
    w.hfK.pre (s.callEntry.withRegions [⟨ou, w.hH.SH.stateBytes⟩]
      [⟨inn, w.hH.SH.stateBytes⟩, ⟨o, w.hH.SH.digestBytes⟩]) := by
  have hS := w.hH.hS; have hD := w.hH.hD
  simp only [HVar.hfK, finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a3, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_uo, h.al, h.sp, h.b_i, h.b_u, h.b_o⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `a2`, into `o`. -/
theorem hf_call {s : State} {inn ou o : Addr} (h : HfArgs w s inn ou o) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, w.H.S⟩, ⟨o, w.H.D⟩] ++ [below s.sp (w.H.fbytes + w.H.F)]) s' →
      (∀ k0 text, k0.length = w.H.B → k0.length + text.length < 2 ^ 64 →
        w.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .a2 = BitVec.ofNat 64 (w.H.B + text.length) →
        w.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o w.H.D = hmacBlockKey w.hH.SH.H k0 text) → Q s') :
    WP isa (.call w.hfN w.H.finalize) s Q := by
  have hS := w.hH.hS; have hD := w.hH.hD; have hB := w.hH.hB
  have hl := w.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : s.callEntry.gpr .a3 = o := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.callAny (k := w.hfK) w.hf_ok (rd := [⟨ou, w.hH.SH.stateBytes⟩])
    (wr := [⟨inn, w.hH.SH.stateBytes⟩, ⟨o, w.hH.SH.digestBytes⟩]) h.pre (by rw [hS, hD]; exact h.hc)
    (by rw [hS, hD]; exact h.hw) ?_ (by have := w.hf_sdepth; have := hl.fbytes; have := hl.F; omega_arith)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [HVar.hfK, finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf w.hf_sdepth (by have := hl.fbytes; have := hl.F; omega_arith)

/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {Q : State → State → Prop} {inn ou o : Addr}
    (h : ∀ s s', Q s s' → HfArgs w s inn ou o ∧ HfArgs w s' inn ou o ∧ s.sp = s'.sp ∧
      s.gpr .a2 = s'.gpr .a2) :
    RelCT isa Q (.call w.hfN w.H.finalize) fun _ _ => True := by
  have hS := w.hH.hS; have hD := w.hH.hD
  refine RelCT.call w.hf_ok w.hfCt [⟨ou, w.hH.SH.stateBytes⟩]
    [⟨inn, w.hH.SH.stateBytes⟩, ⟨o, w.hH.SH.digestBytes⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [HVar.hfK, finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, e2]
  simp only [true_and]
  exact e

end

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st` and the
`len` bytes at `dat`. -/
structure UpdArgs (w : HVar) (s : State) (st dat : Addr) (len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a2 : s.gpr .a2 = dat
  a3 : (s.gpr .a3).toNat = len
  d : Region.Disjoint ⟨dat, len⟩ ⟨st, w.H.S⟩
  al : s.sp.toNat % 16 = 0
  sp : w.H.F ≤ s.sp.toNat
  b_s : (below s.sp w.H.F).Disjoint ⟨st, w.H.S⟩
  b_d : (below s.sp w.H.F).Disjoint ⟨dat, len⟩
  hc : RISCV64.Covers ([⟨dat, len⟩] ++ [⟨st, w.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨st, w.H.S⟩] s.wr

section
variable {w : HVar}

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call {s : State} {st dat : Addr} {len : Nat} (h : UpdArgs w s st dat len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, w.H.S⟩] ++ [below s.sp w.H.F]) s' →
      (∀ m, w.hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        w.hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa (.call w.H.updN w.H.updC) s Q :=
  w.hH.callUpd_ok h.a0 h.a2 h.a3 h.d h.al h.sp h.b_s h.b_d h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

/-- Two runs of a call of the streaming `update` with the same arguments. -/
theorem upd_rel {Q : State → State → Prop} {st dat : Addr} {len : Nat}
    (h : ∀ s s', Q s s' → UpdArgs w s st dat len ∧ UpdArgs w s' st dat len ∧ s.sp = s'.sp ∧
      s.gpr .a1 = s'.gpr .a1) :
    RelCT isa Q (.call w.H.updN w.H.updC) fun _ _ => True := by
  refine RelCT.call w.hH.upd w.t.l.ct.upd [⟨dat, len⟩] [⟨st, w.H.S⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e1⟩ := h s s' hp
  have pre : ∀ {s : State}, UpdArgs w s st dat len →
      (updK w.H.S w.H.F w.hH.SH.Repr).pre (s.callEntry.withRegions [⟨dat, len⟩] [⟨st, w.H.S⟩]) :=
    fun {s} a => by
    have c0 : s.callEntry.gpr .a0 = s.gpr .a0 := State.callEntry_gpr _ (by decide)
    have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
    have c3 : s.callEntry.gpr .a3 = s.gpr .a3 := State.callEntry_gpr _ (by decide)
    simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c0, c2, c3, a.a0, a.a2, a.a3]
    exact ⟨trivial, trivial, a.d, a.al, a.sp, a.b_s, a.b_d⟩
  refine ⟨pre a, pre a', ?_, a.hc, a.hw, a'.hc, a'.hw⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    a.a0, a'.a0, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨e1, BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

end

/-! ## The calls through the table -/

/-- The load of the address of the table's function `j`, at `tab` (in `s6`),
which holds the address of `n`. -/
theorem tload_ok {t : State} {tab : Addr} {j : Nat} (hj : j < 6) (h6 : t.gpr .s6 = tab)
    (hin : InRegions (t.rd ++ t.wr) (tab + BitVec.ofNat 64 (8 * j)) 8)
    (hal : (tab + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0) {a : Addr}
    (hv : t.mem.readW (tab + BitVec.ofNat 64 (8 * j)) 64 = a) :
    WP isa (.block [.load .d .t1 .s6 (8 * j)]) t fun u => Upd t u .t1 a ∧ u.syms = t.syms :=
  VG.RISCV64.WP.of_syms (wp_ld (by omega_using [hj]) (by rw [h6]) hal hin fun u v => WP.block_nil fun sy => by
    rw [hv] at v; exact ⟨v, sy⟩)

/-- The table's function `j`, among `ts`, which reaches `n`: the call of `n`
from the state the load of its address leaves. -/
theorem tcall_ok {t : State} {tab : Addr} {j : Nat} (hj : j < 6) (h6 : t.gpr .s6 = tab)
    (hin : InRegions (t.rd ++ t.wr) (tab + BitVec.ofNat 64 (8 * j)) 8)
    (hal : (tab + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c))
    (hw : t.mem.readW (tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n) {Q : State → Prop}
    (kk : ∀ t', Upd t t' .t1 (t.syms n) → t'.syms = t.syms → WP isa (.call n c) t' Q) :
    WP isa (tcall j ts) t Q := by
  unfold tcall
  refine WP.seq (WP.mono (tload_ok hj h6 hin hal hw) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (kk t' u sy)
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy]; exact hf

/-! ## Two runs -/

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- Code the taint analysis accepts from the registers `rs`, in two runs
whose single-run facts `G₁` and `G₂` agree on them. -/
theorem rel_agree {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa} {rs : List Reg}
    (hag : ∀ s s', P₁ s → P₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' := by
  obtain ⟨_, hc⟩ := hc
  refine ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => ?_) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨e, g⟩ := hag s s' h.1 h.2
  exact ⟨e, fun r hr => g r (Taint.mem_ofRegs.mp hr)⟩

/-- A piece of code, in two runs each described by `WP`. -/
theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A frame that allocates `n` bytes leaks what its body does. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (fun a b => ∃ s₁ s₂, Q s₁ s₂ ∧ a = allocd n s₁ ∧ b = allocd n s₂) body fun _ _ => True) :
    RelCT isa Q (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocd n s := by
    intro s a h'
    simp only [isa, push] at h'
    split at h' <;> cases h'
    rfl
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-- The table's function `j`, among `ts`, which reaches `n` in both runs, at
the same address `a`: two runs of the call of `n` from the states the load of
its address leaves. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {j : Nat} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} {rs : List Reg} {a : Addr} (hcl : Ck rs (.block [.load .d .t1 .s6 (8 * j)]))
    (hag : ∀ s s', Φ₁ s → Φ₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hld₁ : ∀ t, Φ₁ t → WP isa (.block [.load .d .t1 .s6 (8 * j)]) t fun u => Upd t u .t1 a ∧ u.syms = t.syms)
    (hld₂ : ∀ t, Φ₂ t → WP isa (.block [.load .d .t1 .s6 (8 * j)]) t fun u => Upd t u .t1 a ∧ u.syms = t.syms)
    (hf₁ : ∀ t, Φ₁ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hf₂ : ∀ t, Φ₂ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hcall : RelCT isa (fun u u' => (∃ t, Φ₁ t ∧ Upd t u .t1 a ∧ u.syms = t.syms) ∧
      (∃ t', Φ₂ t' ∧ Upd t' u' .t1 a ∧ u'.syms = t'.syms)) (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => Φ₁ t ∧ Φ₂ t') (tcall j ts) fun _ _ => True := by
  unfold tcall
  refine (rel_agree (P₁ := Φ₁) (P₂ := Φ₂) (G₁ := fun u => ∃ t, Φ₁ t ∧ Upd t u .t1 a ∧ u.syms = t.syms)
    (G₂ := fun u => ∃ t, Φ₂ t ∧ Upd t u .t1 a ∧ u.syms = t.syms) hag hcl
    (fun s h => WP.mono (hld₁ s h) fun u ⟨v, y⟩ => ⟨s, h, v, y⟩)
    (fun s h => WP.mono (hld₂ s h) fun u ⟨v, y⟩ => ⟨s, h, v, y⟩)).seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun s _ h => by obtain ⟨t, ht, -⟩ := h.1; simp at hf₁; exact hf₁ t ht
  | cons q ts =>
    refine RelCT.icalls_of_call hcall ?_
    rintro u u' ⟨⟨t, h, v, y⟩, ⟨t', h', v', y'⟩⟩
    refine ⟨a, by show some (u.gpr .t1) = _; rw [v.gpr], by show some (u'.gpr .t1) = _; rw [v'.gpr],
      ?_, ?_, rfl⟩
    · show (q :: ts).find? (fun q => u.syms q.1 == a) = _
      rw [y]; exact hf₁ t h
    · show (q :: ts).find? (fun q => u'.syms q.1 == a) = _
      rw [y']; exact hf₂ t' h'

end VG.Proof.Hkdf.RISCV64

/-! ## `vg_hkdf_key` -/

namespace VG.Proof.Hkdf.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_addSp wp_ld wp_sd)
open VG.Impl.Hkdf.RISCV64
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns tcall)
open VG.Proof.HmacTable.RISCV64 (HVar TabOK TabMem)
open Spec.Hmac (xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let key : Region := ⟨s.gpr .a2, 384⟩
    let tab : Region := ⟨s.gpr .a3, 48⟩
    let stk : Region := below s.sp N
    s.rd = [prk, tab] ∧ s.wr = [key] ∧ prk.Disjoint key ∧ tab.Disjoint key ∧
      s.sp.toNat % 16 = 0 ∧ N ≤ s.sp.toNat ∧ stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 384 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0 ∧
      TabMem w s.syms (s.gpr .a3) s.mem ∧ TabOK w f s.syms
  post s s' := Spec.Hkdf.Keyed w.hH.SH s'.mem (s.gpr .a2) (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_key` uses: its frame, and below it what HMAC's
`init` uses. -/
def keyStack : Nat := kFr + 512

/-- The stack HMAC's functions use, with the hash function's below them. -/
theorem x_le (w : HVar) : w.H.ibytes + w.H.F ≤ 512 ∧ w.H.fbytes + w.H.F ≤ 512 ∧ w.H.F ≤ 512 := by
  have hN := w.hH.hN; have hb := w.hH.hb; have hD := w.hH.hD64
  have hF : w.H.F ≤ 208 := w.t.l.fits
  rcases hb with h | h <;>
    simp only [VG.Impl.Hmac.Stream.RISCV64.Hash.ibytes, VG.Impl.Hmac.Stream.RISCV64.Hash.iso,
      VG.Impl.Hmac.Stream.RISCV64.Hash.fbytes, VG.Impl.Hmac.Stream.RISCV64.Hash.fso,
      VG.Impl.Hmac.Stream.RISCV64.Hash.S, VG.Impl.Hmac.Stream.RISCV64.Hash.B, h] <;> omega_using [hN, hD, hF]

/-- Each streaming state fits in its half of the 384 bytes at `key`. -/
theorem S_le (w : HVar) : w.H.S ≤ 192 := by
  have hN := w.hH.hN; have hB := w.hH.hB64
  show w.H.N + w.H.B ≤ 192
  rcases hB with h | h <;> omega_using [hN, h]

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, and the regions it names. -/
structure KPre (w : HVar) (f : Fns) (s₀ : State) : Prop where
  rd : s₀.rd = [⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩, ⟨s₀.gpr .a3, 48⟩]
  wr : s₀.wr = [⟨s₀.sp, kFr⟩, ⟨s₀.gpr .a2, 384⟩]
  p_k : Region.Disjoint ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩ ⟨s₀.gpr .a2, 384⟩
  t_k : Region.Disjoint ⟨s₀.gpr .a3, 48⟩ ⟨s₀.gpr .a2, 384⟩
  f_p : Region.Disjoint ⟨s₀.sp, kFr⟩ ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩
  f_k : Region.Disjoint ⟨s₀.sp, kFr⟩ ⟨s₀.gpr .a2, 384⟩
  f_t : Region.Disjoint ⟨s₀.sp, kFr⟩ ⟨s₀.gpr .a3, 48⟩
  b_p : (below s₀.sp 512).Disjoint ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩
  b_k : (below s₀.sp 512).Disjoint ⟨s₀.gpr .a2, 384⟩
  b_t : (below s₀.sp 512).Disjoint ⟨s₀.gpr .a3, 48⟩
  b_f : (below s₀.sp 512).Disjoint ⟨s₀.sp, kFr⟩
  al : s₀.sp.toNat % 16 = 0
  sp : 512 ≤ s₀.sp.toNat
  top : s₀.sp.toNat + kFr ≤ 2 ^ 64
  nk : (s₀.gpr .a2).toNat + 384 ≤ 2 ^ 64
  nt : (s₀.gpr .a3).toNat + 48 ≤ 2 ^ 64
  ta : (s₀.gpr .a3).toNat % 8 = 0
  tmem : TabMem w s₀.syms (s₀.gpr .a3) s₀.mem
  tok : TabOK w f s₀.syms

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem kpre_alloc {s : State} (hp : (keyR w f ns keyStack).pre s) : KPre w f (allocd kFr s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hp
  have hfr : kFr = 16 := rfl
  have hN : keyStack = kFr + 512 := rfl
  obtain hspN : (s.sp - BitVec.ofNat 64 kFr).toNat = s.sp.toNat - kFr :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hN] at h6; omega_using [h6]) (by omega_using [hfr])
  obtain subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 kFr, kFr⟩ (below s.sp keyStack) :=
    Offset.sub_below s.sp (by rw [hN]; omega_using []) (by rw [hN]; omega_using [])
  obtain subS : Region.Sub (below (s.sp - BitVec.ofNat 64 kFr) 512) (below s.sp keyStack) := by
    have := below_body' s.sp kFr 512
    rwa [Nat.add_comm 512, ← hN] at this
  refine ⟨h1, by show (⟨s.sp - BitVec.ofNat 64 kFr, kFr⟩ : Region) :: s.wr = _; rw [h2]; rfl, h3, h4,
    h7.sub_left subF, h8.sub_left subF, h9.sub_left subF, h7.sub_left subS, h8.sub_left subS,
    h9.sub_left subS, ?_, ?_, ?_, ?_, h11, h12, h13, h14, h15⟩
  · show (below (s.sp - BitVec.ofNat 64 kFr) 512).Disjoint ⟨s.sp - BitVec.ofNat 64 kFr, kFr⟩
    exact (Offset.base_disjoint_below _ (by have := s.sp.isLt; rw [hN] at h6; omega_arith)).symm
  · show (s.sp - BitVec.ofNat 64 kFr).toNat % 16 = 0
    rw [hspN]; omega_using [hfr, h5]
  · show 512 ≤ (s.sp - BitVec.ofNat 64 kFr).toNat
    rw [hspN]; rw [hN] at h6; omega_using [h6]
  · show (s.sp - BitVec.ofNat 64 kFr).toNat + kFr ≤ 2 ^ 64
    rw [hspN]; have := s.sp.isLt; rw [hN] at h6; omega_using [hfr]

end

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : KPre w f s₀)
include hp

/-- After the prologue: `ra` and `s6` saved, the table in `s6`, and `init`'s
arguments in place. -/
structure KA (w : HVar) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  ra : t.gpr .ra = s₀.gpr .ra
  cs : ∀ r ∈ preserved, r ≠ .s6 → t.gpr r = s₀.gpr r
  s6 : t.gpr .s6 = s₀.gpr .a3
  a0 : t.gpr .a0 = s₀.gpr .a2
  a1 : t.gpr .a1 = s₀.gpr .a2 + BitVec.ofNat 64 192
  a2 : t.gpr .a2 = s₀.gpr .a0
  a3 : t.gpr .a3 = s₀.gpr .a1
  svra : t.mem.readW s₀.sp 64 = s₀.gpr .ra
  svs6 : t.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = s₀.gpr .s6
  frame : Frame [⟨s₀.sp, kFr⟩] s₀.mem t.mem

theorem fr_in {o : Nat} (ho : o + 8 ≤ kFr) : InRegions s₀.wr (s₀.sp + BitVec.ofNat 64 o) 8 := by
  have hfr : kFr = 16 := rfl
  exact ⟨_, by rw [hp.wr]; exact List.mem_cons_self, Offset.contains_base _ ho (by omega_using [ho, hfr])⟩

theorem fr_al {o : Nat} (ho : o % 8 = 0) : (s₀.sp + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hp.al; have := hp.top; have hfr : kFr = 16 := rfl
  omega_arith

/-- The prologue. -/
theorem pro_ok : WP isa (.block keyPro) s₀ (KA w s₀) := by
  have hfr : kFr = 16 := rfl
  unfold keyPro
  refine VG.RISCV64.WP.of_syms (wp_addSp (by decide) fun s₁ u₁ => ?_)
  have e1 : s₁.gpr .t0 + BitVec.ofNat 64 0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero, BitVec.add_zero]
  refine wp_sd (by decide) e1 (by rw [show s₀.sp = s₀.sp + BitVec.ofNat 64 0 by simp]; exact fr_al hp rfl)
    (by rw [u₁.wr, show s₀.sp = s₀.sp + BitVec.ofNat 64 0 by simp]; exact fr_in hp (by rw [hfr]; decide))
    fun s₂ u₂ => ?_
  have e2 : s₂.gpr .t0 + BitVec.ofNat 64 8 = s₀.sp + BitVec.ofNat 64 8 := by
    rw [u₂.gpr, u₁.gpr, BitVec.add_zero]
  refine wp_sd (by decide) e2 (fr_al hp rfl) (by rw [u₂.wr, u₁.wr]; exact fr_in hp (by rw [hfr]))
    fun s₃ u₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ =>
    wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => WP.block_nil fun sy => ?_
  have g : ∀ r, r ≠ .t0 → s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [u₃.gpr, u₂.gpr, u₁.other r hr]
  have m₃ : s₃.mem = (s₀.mem.writeW s₀.sp (s₀.gpr .ra)).writeW (s₀.sp + BitVec.ofNat 64 8) (s₀.gpr .s6) := by
    rw [u₃.mem, u₂.mem, u₂.gpr, u₁.mem, u₁.other .ra (by decide), u₁.other .s6 (by decide)]
  have m₁₀ : s₁₀.mem = s₃.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · exact sy
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · intro r hr h6
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl h6
      | upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · upd_simp [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, g]
  · rw [m₁₀, m₃, Mem.readW_writeW_sep (by
      have := Offset.sep s₀.sp (d := 0) (n := 8) (e := 8) (k := 8) (.inl (Nat.le_refl _)) (by decide) (by decide)
      rwa [BitVec.add_zero] at this) (by decide), Mem.readW_writeW_self64]
  · rw [m₁₀, m₃, Mem.readW_writeW_self64]
  · rw [m₁₀, m₃]
    have hc : ∀ o, o + 8 ≤ kFr → (⟨s₀.sp, kFr⟩ : Region).Contains (s₀.sp + BitVec.ofNat 64 o) (64 / 8) :=
      fun o ho => Offset.contains_base _ ho (by omega_using [ho, hfr])
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (hc 8 (by rw [hfr]))
    have := hc 0 (by rw [hfr]; decide)
    rwa [BitVec.add_zero] at this

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : KPre w f s₀)
include hp

/-- The `PRK` the function keys HMAC with. -/
abbrev prkOf (s₀ : State) : List Byte := bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat

/-- After the call of `init`: the states, and what the prologue left. -/
structure KI (w : HVar) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .s6 → t.gpr r = s₀.gpr r
  svra : t.mem.readW s₀.sp 64 = s₀.gpr .ra
  svs6 : t.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = s₀.gpr .s6
  inn : w.hH.SH.Repr t.mem (s₀.gpr .a2) (xorPad (blockKey w.hH.SH.H (prkOf s₀)) ipad)
  out : w.hH.SH.Repr t.mem (s₀.gpr .a2 + BitVec.ofNat 64 192) (xorPad (blockKey w.hH.SH.H (prkOf s₀)) opad)

omit hp in
theorem prk_len : (s₀.gpr .a1).toNat ≤ 2 ^ 64 := Nat.le_of_lt (s₀.gpr .a1).isLt

/-- The bytes of `PRK` are those on entry outside the frame's writes. -/
theorem prk_frame {m : Mem} (hf : Frame [⟨s₀.sp, kFr⟩] s₀.mem m) :
    bytesAt m (s₀.gpr .a0) (s₀.gpr .a1).toNat = prkOf s₀ :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.f_p.symm) (prk_len (s₀ := s₀)) hi

omit hp in
/-- The states' regions, within `key`. -/
theorem inn_sub : Region.Sub ⟨s₀.gpr .a2, w.H.S⟩ ⟨s₀.gpr .a2, 384⟩ :=
  Region.sub_prefix (by have := S_le w; omega_using [this])

omit hp in
theorem out_sub : Region.Sub ⟨s₀.gpr .a2 + BitVec.ofNat 64 192, w.H.S⟩ ⟨s₀.gpr .a2, 384⟩ :=
  Offset.sub_base _ (by have := S_le w; omega_using [this])

/-- The table's word `0`, the address of HMAC's `init`, as on entry. -/
theorem tab0 {t : State} (h : KA w s₀ t) :
    t.mem.readW (s₀.gpr .a3 + BitVec.ofNat 64 (8 * 0)) 64 = s₀.mem.readW (s₀.gpr .a3) 64 := by
  rw [Nat.mul_zero, BitVec.add_zero]
  have hc := Offset.contains_base (s₀.gpr .a3) (d := 0) (n := 64 / 8) (k := 48) (by decide) (by decide)
  rw [BitVec.add_zero] at hc
  exact h.frame.readW (r := ⟨s₀.gpr .a3, 48⟩) hc
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.f_t.symm) (by decide)

/-- The load of `init`'s address from the table. -/
theorem tload0 {t : State} (h : KA w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 0)]) t fun u => Upd t u .t1 (s₀.syms w.hiN) ∧ u.syms = t.syms :=
  tload_ok (by decide) h.s6 ⟨⟨s₀.gpr .a3, 48⟩, List.mem_append_left _ (by rw [h.rd, hp.rd]; simp),
      Offset.contains_base _ (by decide) (by decide)⟩
    (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp.ta) (by rw [tab0 hp h]; exact hp.tmem.1)

omit hp in
/-- The stack `init` uses, below the frame. -/
theorem hb_init {t : State} (h : KA w s₀ t) :
    Region.Sub (below t.sp (w.H.ibytes + w.H.F)) (below s₀.sp 512) := by
  rw [h.sp]; exact Offset.below_mono _ (x_le w).1 (by decide)

/-- What the call of `init` needs, once the load of its address wrote `t1`. -/
theorem hiArgs {t t' : State} (h : KA w s₀ t) {v : Addr} (u : Upd t t' .t1 v) :
    HiArgs w t' (s₀.gpr .a2) (s₀.gpr .a2 + BitVec.ofNat 64 192) (s₀.gpr .a0) (s₀.gpr .a1).toNat := by
  have hS := S_le w
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.ibytes + w.H.F)) (below s₀.sp 512) := by
    rw [u.sp]; exact hb_init h
  refine ⟨by rw [g _ (by decide), h.a0], by rw [g _ (by decide), h.a1],
      by rw [g _ (by decide), h.a2], by rw [g _ (by decide), h.a3], by rw [u.sp, h.sp]; exact hp.al,
      by rw [u.sp, h.sp]; have := hp.sp; omega_using [this, hx.1],
      (Offset.base_disjoint _ (by omega_using [hS]) (by have := hp.nk; omega_using [this, hS])),
      hp.p_k.sub_right (inn_sub (w := w) (s₀ := s₀)), hp.p_k.sub_right (out_sub (w := w) (s₀ := s₀)),
      (hp.b_k.sub_left hb).sub_right (inn_sub (w := w) (s₀ := s₀)), (hp.b_k.sub_left hb).sub_right (out_sub (w := w) (s₀ := s₀)),
      hp.b_p.sub_left hb, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.rd, u.wr, h.rd, h.wr, hp.rd, hp.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using []⟩
    · exact ⟨⟨s₀.gpr .a2, 384⟩, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨s₀.gpr .a2, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, h.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s₀.gpr .a2, 384⟩, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨s₀.gpr .a2, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩

/-- `init`, called with the table's address in `t1`: the states for `PRK`. -/
theorem init_call {t t' : State} (h : KA w s₀ t) (u : Upd t t' .t1 (s₀.syms w.hiN)) {Q : State → Prop}
    (hQ : ∀ u, KI w s₀ u → Q u) : WP isa (.call w.hiN w.H.init) t' Q := by
  have hS := S_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.ibytes + w.H.F)) (below s₀.sp 512) := by
    rw [u.sp]; exact hb_init h
  have kt' : t'.mem = t.mem := u.mem
  refine hi_call (hiArgs hp h u) fun s' a hI hO => hQ s' ?_
  -- What `init` keeps: everything outside the states and the stack below the frame.
  have fd : ∀ r ∈ ([⟨s₀.gpr .a2, w.H.S⟩, ⟨s₀.gpr .a2 + BitVec.ofNat 64 192, w.H.S⟩] ++
      [below t'.sp (w.H.ibytes + w.H.F)] : List Region), Region.Disjoint ⟨s₀.sp, kFr⟩ r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_k.sub_right (inn_sub (w := w) (s₀ := s₀))
    · exact hp.f_k.sub_right (out_sub (w := w) (s₀ := s₀))
    · exact (hp.b_f.sub_left hb).symm
  have hfr : kFr = 16 := rfl
  have rdW : ∀ o, o + 8 ≤ kFr → s'.mem.readW (s₀.sp + BitVec.ofNat 64 o) 64 =
      t.mem.readW (s₀.sp + BitVec.ofNat 64 o) 64 := fun o ho => by
    rw [← kt']
    exact a.frame.readW (r := ⟨s₀.sp, kFr⟩) (Offset.contains_base _ ho (by omega_using [ho, hfr]))
      fd (by decide)
  refine ⟨a.rd.trans (u.rd.trans h.rd), a.wr.trans (u.wr.trans h.wr), a.sp.trans (u.sp.trans h.sp), ?_,
    ?_, ?_, ?_, ?_⟩
  · intro r hr h6
    have ht1 : r ≠ .t1 := fun e => by subst e; exact absurd hr (by decide)
    rw [a.cs r hr, g r ht1, h.cs r hr h6]
  · have := rdW 0 (by decide); rw [BitVec.add_zero] at this; rw [this, h.svra]
  · rw [rdW 8 (by decide), h.svs6]
  · rw [← prk_frame hp h.frame, ← kt']; exact hI
  · rw [← prk_frame hp h.frame, ← kt']; exact hO

/-- `init`, through the table: the states for `PRK`. -/
theorem init_ok {t : State} (h : KA w s₀ t) {Q : State → Prop} (hQ : ∀ u, KI w s₀ u → Q u) :
    WP isa (tcall 0 f.init) t Q := by
  unfold tcall
  refine WP.seq (WP.mono (tload0 hp h) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (init_call hp h u hQ)
  show f.init.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, h.sy]; exact hp.tok.i

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : KPre w f s₀)
include hp

/-- The epilogue: `ra` and `s6` restored. -/
theorem epi_ok {t : State} (h : KI w s₀ t) :
    WP isa (.block keyEpi) t fun v => v.gpr .ra = s₀.gpr .ra ∧ (∀ r ∈ preserved, v.gpr r = s₀.gpr r) ∧
      v.sp = s₀.sp ∧ v.wr = s₀.wr ∧ v.mem = t.mem := by
  have hfr : kFr = 16 := rfl
  have hin : ∀ o, o + 8 ≤ kFr → InRegions (t.rd ++ t.wr) (s₀.sp + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨⟨s₀.sp, kFr⟩, List.mem_append_right _ (by rw [h.wr, hp.wr]; exact List.mem_cons_self),
      Offset.contains_base _ ho (by omega_using [ho, hfr])⟩
  unfold keyEpi
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have e₁ : t₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero, h.sp]
  refine wp_ld (by decide) (a := s₀.sp) (by rw [e₁, BitVec.add_zero])
    (by rw [show s₀.sp = s₀.sp + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]; exact fr_al hp rfl)
    (by rw [u₁.rd, u₁.wr, show s₀.sp = s₀.sp + BitVec.ofNat 64 0 by rw [BitVec.add_zero]];
        exact hin 0 (by rw [hfr]; decide)) fun t₂ u₂ => ?_
  refine wp_ld (by decide) (a := s₀.sp + BitVec.ofNat 64 8) (by rw [u₂.other _ (by decide), e₁])
    (fr_al hp rfl) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 8 (by rw [hfr])) fun t₃ u₃ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact h.svra, fun r hr => ?_,
    by rw [u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [u₃.mem, m₂]⟩
  by_cases h6 : r = .s6
  · subst h6; rw [u₃.gpr, m₂]; exact h.svs6
  · have ht0 : r ≠ .t0 := fun e => by subst e; exact absurd hr (by decide)
    have hra : r ≠ .ra := fun e => by subst e; exact absurd hr (by decide)
    rw [u₃.other r h6, u₂.other r hra, u₁.other r ht0, h.cs r hr h6]

end

/-- `vg_hkdf_key`, in its frame. -/
theorem key_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hp : (keyR w f ns keyStack).pre s) :
    WP isa (key f) s fun s' => abiPreserved s s' ∧ (keyR w f ns keyStack).post s s' := by
  have hfr : kFr = 16 := rfl
  have hsp : keyStack ≤ s.sp.toNat := hp.2.2.2.2.2.1
  obtain p := kpre_alloc hp
  unfold key keyMain
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have : keyStack = kFr + 512 := rfl; omega_using [hsp, this])
    (WP.seq (WP.mono (pro_ok p) fun t ht => WP.seq (init_ok p ht fun u hu =>
      WP.mono (epi_ok p hu) fun v ⟨hra, hcs, hvsp, hvwr, hvm⟩ m un fl => ?_)))
  have hS := S_le w
  refine ⟨⟨fun r hr => hcs r hr, ?_, hra⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 kFr = s.sp
    rw [hvsp]; simp only [allocd, BitVec.sub_add_cancel]
  -- The `free` loses the frame's bytes, which lie apart from `key`.
  have keep : ∀ o, o + w.H.S ≤ 384 → ∀ i < w.H.S,
      m (s.gpr .a2 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = v.mem (s.gpr .a2 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => lost_byte fl (R := ⟨s.gpr .a2 + BitVec.ofNat 64 o, w.H.S⟩)
      (p.f_k.sub_right (Offset.sub_base _ ho)).symm hi
  have k0 := keep 0 (by omega_using [hS])
  rw [BitVec.add_zero] at k0
  refine ⟨w.hH.congr _ _ _ _ (fun i hi => k0 i hi) (by rw [hvm]; exact hu.inn),
    w.hH.congr _ _ _ _ (fun i hi => keep 192 (by omega_using [hS]) i hi) (by rw [hvm]; exact hu.out)⟩

/-! ## Constant time -/

/-- The taint checks of the pieces of `vg_hkdf_key` between the calls. -/
structure KChecks : Prop where
  pro : Ck [.a0, .a1, .a2, .a3] (.block keyPro)
  tl : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 0)])
  epi : Ck [] (.block keyEpi)

theorem kchecks : KChecks := by
  refine ⟨?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- `vg_hkdf_key` is constant time: two runs whose public data agree leak the
same trace. -/
theorem key_ct {w : HVar} {f : Fns} {ns : List String} (hns : w.hiN ∈ ns) :
    ConstantTime isa (keyR w f ns keyStack).pre (keyR w f ns keyStack).pub (key f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := kpre_alloc h; have hp' := kpre_alloc h'
  obtain ⟨qsp, q0, q1, q2, q3, qn⟩ := hpub
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (key f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold key
  refine rel_alloc ((?_ : RelCT isa (fun s s' => s = allocd kFr e ∧ s' = allocd kFr e') (keyMain f)
    fun _ _ => True).mono ?_ fun _ _ h => h)
  rotate_left
  · rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  have hsp : (allocd kFr e).sp = (allocd kFr e').sp := by simp only [allocd, qsp]
  have hsy : (allocd kFr e).syms w.hiN = (allocd kFr e').syms w.hiN := qn _ hns
  replace q0 : (allocd kFr e).gpr .a0 = (allocd kFr e').gpr .a0 := q0
  replace q1 : (allocd kFr e).gpr .a1 = (allocd kFr e').gpr .a1 := q1
  replace q2 : (allocd kFr e).gpr .a2 = (allocd kFr e').gpr .a2 := q2
  replace q3 : (allocd kFr e).gpr .a3 = (allocd kFr e').gpr .a3 := q3
  generalize allocd kFr e = s₀ at hp hsp hsy q0 q1 q2 q3 ⊢
  generalize allocd kFr e' = s₀' at hp' hsp hsy q0 q1 q2 q3 ⊢
  have kc := kchecks
  unfold keyMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := KA w s₀) (G₂ := KA w s₀')
    (rs := [.a0, .a1, .a2, .a3]) (fun s s' hs hs' => by
      subst hs hs'
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3]) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => KA w s₀ t ∧ KA w s₀' t') (tcall 0 f.init)
      fun t t' => KI w s₀ t ∧ KI w s₀' t' := by
    refine rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.hiN) kc.tl (fun t t' k k' => ⟨by rw [k.sp, k'.sp, hsp],
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [k.s6, k'.s6]; exact q3⟩)
      (fun t k => tload0 hp k) (fun t k => by rw [hsy]; exact tload0 hp' k)
      (fun t k => by rw [k.sy]; exact hp.tok.i) (fun t k => by rw [k.sy, hsy]; exact hp'.tok.i) ?_)
      (fun t k => init_ok hp k fun _ h => h) (fun t k => init_ok hp' k fun _ h => h)
    refine hi_rel fun u u' ⟨⟨t, k, v, _⟩, ⟨t', k', v', _⟩⟩ => ⟨hiArgs hp k v, ?_, by rw [v.sp, v'.sp, k.sp, k'.sp, hsp]⟩
    have := hiArgs hp' k' v'
    rwa [← q0, ← q1, ← q2] at this
  have r3 := rel_agree (P₁ := KI w s₀) (P₂ := KI w s₀') (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' k k' => ⟨by rw [k.sp, k'.sp, hsp], fun _ h => absurd h List.not_mem_nil⟩) kc.epi
    (fun t k => WP.mono (epi_ok hp k) fun _ _ => trivial) (fun t k => WP.mono (epi_ok hp' k) fun _ _ => trivial)
  exact ((r1.seq (r2.seq r3)).mono (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.Hkdf.RISCV64
