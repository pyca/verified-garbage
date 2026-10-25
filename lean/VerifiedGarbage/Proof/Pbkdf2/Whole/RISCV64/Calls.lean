module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Covers

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the calls

The calls of HMAC's `init` and `finalize` (against the contracts of their
generic proofs, `WP.callAny`, since they allocate their working space on the
stack), of `iterate` (against `iterK`, `WP.call`, since it pushes no frames)
and of the streaming `update` (`HashOK.callUpd_ok`): what each needs of the
state it is called from, and what holds when it returns; and, for the first
three, that two runs of the call with the same arguments leak the same
trace (`RelCT.call`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open VG.Proof.Pbkdf2.RISCV64 (iterK)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns} (hF : FnsOK F)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-! ## HMAC's `init` -/

theorem hi_sdepth (hH : HashOK F.H) : sdepth F.H.init ≤ F.H.ibytes + F.H.F := by
  have := hH.initSd; have := hH.updSd; have := hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes]
  omega

theorem hf_sdepth (hH : HashOK F.H) : sdepth F.H.finalize ≤ F.H.fbytes + F.H.F := by
  have := hH.updSd; have := hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega

theorem hi_ok : ∀ s, (hiK F.H hF.hH.SH).pre s → ∃ t s', Exec isa F.H.init s t s' ∧
    abiPreserved s s' ∧ (hiK F.H hF.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Init.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

theorem hf_ok : ∀ s, (hfK F.H hF.hH.SH).pre s → ∃ t s', Exec isa F.H.finalize s t s' ∧
    abiPreserved s s' ∧ (hfK F.H hF.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Finalize.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (F : Fns) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a2 : s.gpr .a2 = k
  a3 : (s.gpr .a3).toNat = kl
  al : s.sp.toNat % 16 = 0
  sp : F.H.ibytes + F.H.F ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_ki : Region.Disjoint ⟨k, kl⟩ ⟨inn, F.H.S⟩
  d_ko : Region.Disjoint ⟨k, kl⟩ ⟨ou, F.H.S⟩
  b_i : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨inn, F.H.S⟩
  b_o : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨ou, F.H.S⟩
  b_k : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨k, kl⟩
  hc : RISCV64.Covers ([⟨k, kl⟩] ++ [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] s.wr

include hF in
theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs F s inn ou k kl) :
    (hiK F.H hF.hH.SH).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) := by
  have hS := hF.hH.hS
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, hS]
  exact ⟨trivial, trivial, h.d_io, h.d_ki, h.d_ko, h.al, h.sp, h.b_i, h.b_o, h.b_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs F s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] ++ [below s.sp (F.H.ibytes + F.H.F)]) s' →
      hF.hH.SH.Repr s'.mem inn (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hF.hH.SH.Repr s'.mem ou (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa F.callHi s Q := by
  have hS := hF.hH.hS
  have hl := hF.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = k := (State.callEntry_gpr _ (by decide)).trans h.a2
  have c3 : (s.callEntry.gpr .a3).toNat = kl := by rw [State.callEntry_gpr _ (by decide), h.a3]
  refine WP.callAny (k := hiK F.H hF.hH.SH) (hi_ok hF) (rd := [⟨k, kl⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) (h.pre hF) (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := hi_sdepth hF.hH; have := hl.ibytes; have := hl.F; omega)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
    c3] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf (hi_sdepth hF.hH) (by have := hl.ibytes; have := hl.F; omega)

include hF in
/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {P : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs F s inn ou k kl ∧ HiArgs F s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa P F.callHi fun _ _ => True := by
  have hS := hF.hH.hS
  refine RelCT.call (hi_ok hF) hF.hiCt [⟨k, kl⟩] [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou` and `out` at `o`. -/
structure HfArgs (F : Fns) (s : State) (inn ou o : Addr) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a3 : s.gpr .a3 = o
  al : s.sp.toNat % 16 = 0
  sp : F.H.fbytes + F.H.F ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨o, F.H.D⟩
  d_uo : Region.Disjoint ⟨ou, F.H.S⟩ ⟨o, F.H.D⟩
  b_i : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨inn, F.H.S⟩
  b_u : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨ou, F.H.S⟩
  b_o : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨o, F.H.D⟩
  hc : RISCV64.Covers ([⟨ou, F.H.S⟩] ++ [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩] s.wr

include hF in
theorem HfArgs.pre {s : State} {inn ou o : Addr} (h : HfArgs F s inn ou o) :
    (hfK F.H hF.hH.SH).pre (s.callEntry.withRegions [⟨ou, hF.hH.SH.stateBytes⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩]) := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a3, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_uo, h.al, h.sp, h.b_i, h.b_u, h.b_o⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `a2`, into `o`. -/
theorem hf_call {s : State} {inn ou o : Addr} (h : HfArgs F s inn ou o) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨o, F.H.D⟩] ++ [below s.sp (F.H.fbytes + F.H.F)]) s' →
      (∀ k0 text, k0.length = F.H.B → k0.length + text.length < 2 ^ 64 →
        hF.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .a2 = BitVec.ofNat 64 (F.H.B + text.length) →
        hF.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o F.H.D = hmacBlockKey hF.hH.SH.H k0 text) → Q s') :
    WP isa F.callHf s Q := by
  have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have hl := hF.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : s.callEntry.gpr .a3 = o := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.callAny (k := hfK F.H hF.hH.SH) (hf_ok hF) (rd := [⟨ou, hF.hH.SH.stateBytes⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩]) (h.pre hF) (by rw [hS, hD]; exact h.hc)
    (by rw [hS, hD]; exact h.hw) ?_ (by have := hf_sdepth hF.hH; have := hl.fbytes; have := hl.F; omega)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf (hf_sdepth hF.hH) (by have := hl.fbytes; have := hl.F; omega)

include hF in
/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {P : State → State → Prop} {inn ou o : Addr}
    (h : ∀ s s', P s s' → HfArgs F s inn ou o ∧ HfArgs F s' inn ou o ∧ s.sp = s'.sp ∧
      s.gpr .a2 = s'.gpr .a2) :
    RelCT isa P F.callHf fun _ _ => True := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (hf_ok hF) hF.hfCt [⟨ou, hF.hH.SH.stateBytes⟩]
    [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, e2]
  simp only [true_and]
  exact e

/-! ## `iterate` -/

/-- What a call of `iterate` needs: the key's states at `key`, `U` at `u`,
`T` at `t` and the working space at `sc`. -/
structure ItArgs (F : Fns) (s : State) (key u t sc : Addr) : Prop where
  a0 : s.gpr .a0 = key
  a1 : s.gpr .a1 = u
  a3 : s.gpr .a3 = t
  a4 : s.gpr .a4 = sc
  d_kt : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨t, F.H.D⟩
  d_ks : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨sc, F.itW⟩
  d_ut : Region.Disjoint ⟨u, F.H.D⟩ ⟨t, F.H.D⟩
  d_us : Region.Disjoint ⟨u, F.H.D⟩ ⟨sc, F.itW⟩
  d_ts : Region.Disjoint ⟨t, F.H.D⟩ ⟨sc, F.itW⟩
  hc : RISCV64.Covers ([⟨key, 2 * F.H.S⟩, ⟨u, F.H.D⟩] ++ [⟨t, F.H.D⟩, ⟨sc, F.itW⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨t, F.H.D⟩, ⟨sc, F.itW⟩] s.wr

include hF in
theorem ItArgs.pre {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) :
    (iterK hF.hH.SH F.itW).pre (s.callEntry.withRegions
      [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
      [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩]) := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs),
    h.a0, h.a1, h.a3, h.a4, hS, hD]
  exact ⟨trivial, trivial, h.d_kt, h.d_ks, h.d_ut, h.d_us, h.d_ts⟩

/-- `iterate` with the key's states at `key`, `U` at `u`, `n` in `a2`, `T` at
`t` and the working space at `sc`. -/
theorem it_call {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨t, F.H.D⟩, ⟨sc, F.itW⟩] s' →
      (∀ k0, k0.length = F.H.B → hF.hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hF.hH.SH.Repr s.mem (key + BitVec.ofNat 64 F.H.S) (xorPad k0 opad) →
        bytesAt s'.mem t F.H.D = Spec.Pbkdf2.iterate (hmacBlockKey hF.hH.SH.H k0)
          ((s.gpr .a2).setWidth 32).toNat (bytesAt s.mem u F.H.D) (bytesAt s.mem t F.H.D)) → Q s') :
    WP isa F.callIt s Q := by
  have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have c0 : s.callEntry.gpr .a0 = key := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = u := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : s.callEntry.gpr .a3 = t := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.call (k := iterK hF.hH.SH F.itW) hF.itOk (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hD]; exact h.hw) ?_ hF.itNf
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB, hS] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hD] at hf
  exact hf

include hF in
/-- Two runs of a call of `iterate` with the same arguments. -/
theorem it_rel {P : State → State → Prop} {key u t sc : Addr}
    (h : ∀ s s', P s s' → ItArgs F s key u t sc ∧ ItArgs F s' key u t sc ∧ s.sp = s'.sp ∧
      (s.gpr .a2).setWidth 32 = (s'.gpr .a2).setWidth 32) :
    RelCT isa P F.callIt fun _ _ => True := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call hF.itOk hF.itCt [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
    [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hD]; exact a'.hw⟩
  simp only [iterK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a4 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, a.a4, a'.a4, e2]
  simp only [true_and]
  exact e

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st` and the
`len` bytes at `dat`. -/
structure UpdArgs (F : Fns) (s : State) (st dat : Addr) (len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a2 : s.gpr .a2 = dat
  a3 : (s.gpr .a3).toNat = len
  d : Region.Disjoint ⟨dat, len⟩ ⟨st, F.H.S⟩
  al : s.sp.toNat % 16 = 0
  sp : F.H.F ≤ s.sp.toNat
  b_s : (below s.sp F.H.F).Disjoint ⟨st, F.H.S⟩
  b_d : (below s.sp F.H.F).Disjoint ⟨dat, len⟩
  hc : RISCV64.Covers ([⟨dat, len⟩] ++ [⟨st, F.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨st, F.H.S⟩] s.wr

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call (hH : HashOK F.H) {s : State} {st dat : Addr} {len : Nat} (h : UpdArgs F s st dat len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, F.H.S⟩] ++ [below s.sp F.H.F]) s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa F.H.callUpd s Q :=
  hH.callUpd_ok h.a0 h.a2 h.a3 h.d h.al h.sp h.b_s h.b_d h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Pbkdf2.Whole.RISCV64
