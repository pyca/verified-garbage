module

public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Impl.Hkdf.PPC64LE
public import VerifiedGarbage.Spec.Hkdf.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Hkdf.PPC64LE

/-!
# HKDF on PPC64LE: the calls of a table's HMAC functions, and `vg_hkdf_key`, correct

## The calls

For a hash function with HMAC on PPC64LE (`HVar`): what a call of HMAC's
`init` for a key of any length (`any_call`, a table's word 0, `HVar.anyV`),
the streaming `update` (`upd_call`) or HMAC's `finalize` (`fin_call`) needs
of the state it is called from (`AnyArgs`, `UpdArgs`, `FinArgs`), with their
working space as an argument, and what holds when it returns (`After`):
memory changed only in the regions it writes and the stack below the stack
pointer it uses (144 bytes for `init`, whose code for a key longer than a
block calls `init` for a shorter one in a frame of its own, `HVar.any_sd`;
48 for `update`; 96 for `finalize`, `HVar.fin_sd`); that two runs of each
with the same arguments leak the same trace (`any_rel`, `upd_rel`,
`fin_rel`); and the indirect call of the table's function `j` (`tcall`), at
the address the table holds, which is the function's (`tcall_ok`,
`tcall_rel`).

## `vg_hkdf_key`

The contract the proof is written against (`keyR`), for the table `hmac` of
one hash function `w`, whose functions an indirect call of `f`'s reaches:
`key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold HMAC's
states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming states).
The stack the function uses (`keyStack` bytes) is, from its lowest byte `L`
up, the 144 bytes `init` uses and the frame (`kFr` bytes), whose return
address slot and working space are at offsets of `L` (`KPre`). The prologue
saves the return address and moves `init`'s arguments into place (`pro_ok`);
`init`, through the table, writes the states (`init_ok`); the epilogue
restores the return address, which nothing else wrote (`epi_ok`).
-/

@[expose] public section

namespace VG.Proof.HmacTable.PPC64LE.HVar

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

variable (w : HVar)

/-- The states of `w`'s instance are `w`'s streaming states. -/
theorem hS : w.I.S.stateBytes = w.H.S := by rw [w.hIS]; exact w.ok.hS

theorem hD : w.I.S.digestBytes = w.H.D := by rw [w.hIS]; exact w.ok.hD

theorem hB : w.I.S.H.blockSize = w.H.B := by rw [w.hIS]; exact w.ok.hB

/-- HMAC's `init` for a key of any length, a table's word 0, uses at most
144 bytes of stack: `initLong`'s frame, `init`'s and the streaming
functions'. -/
theorem any_sd : sdepth w.initC ≤ 144 := by
  have h₁ := sdepth_le_fdepth w.H.initLong (by
    simp [Hash.initLong, pushFrames, Instr.isPush,
      Proof.Hmac.Stream.PPC64LE.InitLong.initLongMain_pf w.ok])
  have h₂ : w.H.initLong.fdepth ≤ 3 := by
    have := Proof.Hmac.Stream.PPC64LE.InitLong.initLongMain_fdepth w.ok
    simp only [Hash.initLong, Code.fdepth, Nat.max_le]; omega_arith
  have h₃ := sdepth_le_fdepth w.H.init (Proof.Hmac.Stream.PPC64LE.InitLong.init_pf w.ok)
  have h₄ := Proof.Hmac.Stream.PPC64LE.InitLong.init_fdepth w.ok
  simp only [HVar.initC, Hash.initAny, Hash.initEntry, Code.iteCold, sdepth, Nat.max_le, Nat.zero_max,
    Nat.max_zero]
  omega_arith

/-- HMAC's `finalize` uses at most 96 bytes of stack. -/
theorem fin_sd : sdepth w.H.finalize ≤ 96 := by
  have h₁ := sdepth_le_fdepth w.H.finalize (by
    simp [Hash.finalize, pushFrames, Instr.isPush, Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf w.ok])
  have h₂ : w.H.finalize.fdepth ≤ 2 := by
    have := Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth w.ok
    simp only [Hash.finalize, Code.fdepth, Nat.max_le]; omega_arith
  omega_arith

end VG.Proof.HmacTable.PPC64LE.HVar

namespace VG.Proof.Hkdf.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK updK)
open VG.Proof.HmacTable.PPC64LE (HVar anyScratchContract TabOK TabMem)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- What a call leaves: the regions, the stack pointer, the addresses of
the statics, the callee-saved registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sy : s'.syms = s.syms
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-! ## HMAC's `init` for a key of any length -/

/-- What a call of HMAC's `init` for a key of any length needs of the state
it is called from: the states at `inn` and `ou`, the key's `kl` bytes at `k`
and the working space at `sc`. -/
structure AnyArgs (w : HVar) (s : State) (inn ou k sc : Addr) (kl : Nat) : Prop where
  r3 : s.gpr .r3 = inn
  r4 : s.gpr .r4 = ou
  r5 : s.gpr .r5 = k
  r6 : (s.gpr .r6).toNat = kl
  r7 : s.gpr .r7 = sc
  sp : 144 ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, w.H.S⟩ ⟨ou, w.H.S⟩
  d_ik : Region.Disjoint ⟨inn, w.H.S⟩ ⟨k, kl⟩
  d_is : Region.Disjoint ⟨inn, w.H.S⟩ ⟨sc, w.I.scratch * 8⟩
  d_ok : Region.Disjoint ⟨ou, w.H.S⟩ ⟨k, kl⟩
  d_os : Region.Disjoint ⟨ou, w.H.S⟩ ⟨sc, w.I.scratch * 8⟩
  d_ks : Region.Disjoint ⟨k, kl⟩ ⟨sc, w.I.scratch * 8⟩
  b_i : (below s.sp 144).Disjoint ⟨inn, w.H.S⟩
  b_o : (below s.sp 144).Disjoint ⟨ou, w.H.S⟩
  b_k : (below s.sp 144).Disjoint ⟨k, kl⟩
  b_s : (below s.sp 144).Disjoint ⟨sc, w.I.scratch * 8⟩
  n_i : inn.toNat + w.H.S ≤ 2 ^ 64
  n_o : ou.toNat + w.H.S ≤ 2 ^ 64
  n_k : k.toNat + kl ≤ 2 ^ 64
  n_s : sc.toNat + w.I.scratch * 8 ≤ 2 ^ 64
  hc : Covers ([⟨k, kl⟩] ++ [⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩, ⟨sc, w.I.scratch * 8⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩, ⟨sc, w.I.scratch * 8⟩] s.wr

section
variable {w : HVar}

theorem AnyArgs.pre {s : State} {inn ou k sc : Addr} {kl : Nat} (h : AnyArgs w s inn ou k sc kl) :
    (anyScratchContract w.I.S w.I.scratch).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, w.I.S.stateBytes⟩, ⟨ou, w.I.S.stateBytes⟩, ⟨sc, w.I.scratch * 8⟩]) := by
  have hS := w.hS
  sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs,
    stackBelow]
  simp only [h.r3, h.r4, h.r5, h.r6, h.r7, hS]
  exact ⟨h.sp, trivial, trivial, h.d_io, h.d_ik, h.d_is, h.d_ok, h.d_os, h.d_ks, h.b_i, h.b_o, h.b_k, h.b_s,
    h.n_i, h.n_o, h.n_k, h.n_s⟩

/-- HMAC's `init` for a key of any length: the key's `kl` bytes at `k`, into
the states at `inn` and `ou`, with the working space at `sc`. -/
theorem any_call {s : State} {inn ou k sc : Addr} {kl : Nat} (h : AnyArgs w s inn ou k sc kl)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, w.H.S⟩, ⟨ou, w.H.S⟩, ⟨sc, w.I.scratch * 8⟩] ++ [below s.sp 144]) s' →
      w.ok.SH.Repr s'.mem inn (xorPad (blockKey w.ok.SH.H (bytesAt s.mem k kl)) ipad) →
      w.ok.SH.Repr s'.mem ou (xorPad (blockKey w.ok.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call w.initN w.initC) s Q := by
  have hS := w.hS
  have hd := w.any_sd
  refine WP.of_syms (WP.callAny (k := anyScratchContract w.I.S w.I.scratch) w.anyV.1 (rd := [⟨k, kl⟩])
    (wr := [⟨inn, w.I.S.stateBytes⟩, ⟨ou, w.I.S.stateBytes⟩, ⟨sc, w.I.scratch * 8⟩]) h.pre
    (by rw [hS]; exact h.hc) (by rw [hS]; exact h.hw) ?_ (by omega_using [hd]))
  intro s' hrd hwr hsp hf hcs hpost sy
  sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs,
    stackBelow] at hpost
  simp only [h.r3, h.r4, h.r5, h.r6] at hpost
  rw [hS] at hf
  rw [w.hIS] at hpost
  exact hQ s' ⟨hrd, hwr, hsp, sy, hcs, Frame.below_mono hf hd (by decide)⟩ hpost.1 hpost.2

/-- Two runs of a call of HMAC's `init` for a key of any length with the same
arguments. -/
theorem any_rel {Q : State → State → Prop} {inn ou k sc : Addr} {kl : Nat}
    (h : ∀ s s', Q s s' → AnyArgs w s inn ou k sc kl ∧ AnyArgs w s' inn ou k sc kl ∧ s.sp = s'.sp) :
    RelCT isa Q (.call w.initN w.initC) fun _ _ => True := by
  have hS := w.hS
  refine RelCT.call w.anyV.1 w.anyV.2.1 [⟨k, kl⟩]
    [⟨inn, w.I.S.stateBytes⟩, ⟨ou, w.I.S.stateBytes⟩, ⟨sc, w.I.scratch * 8⟩] fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
  simp only [a.r3, a'.r3, a.r4, a'.r4, a.r5, a'.r5, a.r7, a'.r7, e, true_and]
  exact ⟨BitVec.eq_of_toNat_eq (a.r6.trans a'.r6.symm), trivial⟩

end

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st`, the
`len` bytes at `dat` and the working space at `sc`. -/
structure UpdArgs (w : HVar) (s : State) (st dat sc : Addr) (len : Nat) : Prop where
  r3 : s.gpr .r3 = st
  r5 : s.gpr .r5 = dat
  r6 : (s.gpr .r6).toNat = len
  r7 : s.gpr .r7 = sc
  d_ss : Region.Disjoint ⟨st, w.H.S⟩ ⟨sc, w.H.W⟩
  d_ds : Region.Disjoint ⟨dat, len⟩ ⟨st, w.H.S⟩
  d_dw : Region.Disjoint ⟨dat, len⟩ ⟨sc, w.H.W⟩
  sp : 48 ≤ s.sp.toNat
  b_s : (below s.sp 48).Disjoint ⟨st, w.H.S⟩
  b_d : (below s.sp 48).Disjoint ⟨dat, len⟩
  b_w : (below s.sp 48).Disjoint ⟨sc, w.H.W⟩
  hc : Covers ([⟨dat, len⟩] ++ [⟨st, w.H.S⟩, ⟨sc, w.H.W⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨st, w.H.S⟩, ⟨sc, w.H.W⟩] s.wr

section
variable {w : HVar}

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call {s : State} {st dat sc : Addr} {len : Nat} (h : UpdArgs w s st dat sc len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, w.H.S⟩, ⟨sc, w.H.W⟩] ++ [below s.sp 48]) s' →
      (∀ m, w.ok.SH.Repr s.mem st m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        w.ok.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa (.call w.H.updN w.H.updC) s Q :=
  WP.of_syms (w.ok.callUpd_ok h.r3 h.r5 h.r6 h.r7 h.d_ss h.d_ds h.d_dw h.sp h.b_s h.b_d h.b_w h.hc h.hw
    fun s' a b c d e f sy => hQ s' ⟨a, b, c, sy, e, d⟩ f)

/-- Two runs of a call of the streaming `update` with the same arguments. -/
theorem upd_rel {Q : State → State → Prop} {st dat sc : Addr} {len : Nat}
    (h : ∀ s s', Q s s' → UpdArgs w s st dat sc len ∧ UpdArgs w s' st dat sc len ∧ s.sp = s'.sp ∧
      s.gpr .r4 = s'.gpr .r4) :
    RelCT isa Q (.call w.H.updN w.H.updC) fun _ _ => True := by
  refine RelCT.call w.ok.upd w.ct.upd [⟨dat, len⟩] [⟨st, w.H.S⟩, ⟨sc, w.H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e4⟩ := h s s' hp
  have pre : ∀ {s : State}, UpdArgs w s st dat sc len →
      (updK w.H.S w.H.W w.ok.SH.Repr).pre (s.callEntry.withRegions [⟨dat, len⟩] [⟨st, w.H.S⟩, ⟨sc, w.H.W⟩]) :=
    fun {s} a => by
    have c3 : s.callEntry.gpr .r3 = s.gpr .r3 := State.callEntry_gpr _ (by decide)
    have c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
    have c6 : s.callEntry.gpr .r6 = s.gpr .r6 := State.callEntry_gpr _ (by decide)
    have c7 : s.callEntry.gpr .r7 = s.gpr .r7 := State.callEntry_gpr _ (by decide)
    simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c3, c5, c6, c7, a.r3, a.r5, a.r6, a.r7]
    exact ⟨trivial, trivial, a.d_ss, a.d_ds, a.d_dw, a.sp, a.b_s, a.b_d, a.b_w⟩
  refine ⟨pre a, pre a', ?_, a.hc, a.hw, a'.hc, a'.hw⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r7 ∉ linkRegs by decide), a.r3, a'.r3, a.r5, a'.r5, a.r7, a'.r7, e4, e, true_and,
    and_true]
  exact BitVec.eq_of_toNat_eq (a.r6.trans a'.r6.symm)

end

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou`, `out` at `o` and the working space at `sc`. -/
structure FinArgs (w : HVar) (s : State) (inn ou o sc : Addr) : Prop where
  r3 : s.gpr .r3 = inn
  r4 : s.gpr .r4 = ou
  r6 : s.gpr .r6 = o
  r7 : s.gpr .r7 = sc
  d_iu : Region.Disjoint ⟨inn, w.H.S⟩ ⟨ou, w.H.S⟩
  d_io : Region.Disjoint ⟨inn, w.H.S⟩ ⟨o, w.H.D⟩
  d_is : Region.Disjoint ⟨inn, w.H.S⟩ ⟨sc, w.I.scratch * 8⟩
  d_uo : Region.Disjoint ⟨ou, w.H.S⟩ ⟨o, w.H.D⟩
  d_us : Region.Disjoint ⟨ou, w.H.S⟩ ⟨sc, w.I.scratch * 8⟩
  d_os : Region.Disjoint ⟨o, w.H.D⟩ ⟨sc, w.I.scratch * 8⟩
  sp : 96 ≤ s.sp.toNat
  b_i : (below s.sp 96).Disjoint ⟨inn, w.H.S⟩
  b_u : (below s.sp 96).Disjoint ⟨ou, w.H.S⟩
  b_o : (below s.sp 96).Disjoint ⟨o, w.H.D⟩
  b_s : (below s.sp 96).Disjoint ⟨sc, w.I.scratch * 8⟩
  n_i : inn.toNat + w.H.S ≤ 2 ^ 64
  n_u : ou.toNat + w.H.S ≤ 2 ^ 64
  n_o : o.toNat + w.H.D ≤ 2 ^ 64
  n_s : sc.toNat + w.I.scratch * 8 ≤ 2 ^ 64
  hc : Covers ([⟨ou, w.H.S⟩] ++ [⟨inn, w.H.S⟩, ⟨o, w.H.D⟩, ⟨sc, w.I.scratch * 8⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, w.H.S⟩, ⟨o, w.H.D⟩, ⟨sc, w.I.scratch * 8⟩] s.wr

section
variable {w : HVar}

theorem FinArgs.pre {s : State} {inn ou o sc : Addr} (h : FinArgs w s inn ou o sc) :
    (Proof.Hmac.Instance.finalizeScratchContract w.I PPC64LE.abi 96).pre (s.callEntry.withRegions
      [⟨ou, w.I.S.stateBytes⟩] [⟨inn, w.I.S.stateBytes⟩, ⟨o, w.I.S.digestBytes⟩, ⟨sc, w.I.scratch * 8⟩]) := by
  have hS := w.hS
  have hD := w.hD
  sig_pre [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  simp only [h.r3, h.r4, h.r6, h.r7, hS, hD]
  exact ⟨h.sp, trivial, trivial, h.d_iu, h.d_io, h.d_is, h.d_uo, h.d_us, h.d_os, h.b_i, h.b_u, h.b_o, h.b_s,
    h.n_i, h.n_u, h.n_o, h.n_s⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `r5`, into `o`, with the working space at `sc`. -/
theorem fin_call {s : State} {inn ou o sc : Addr} (h : FinArgs w s inn ou o sc) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, w.H.S⟩, ⟨o, w.H.D⟩, ⟨sc, w.I.scratch * 8⟩] ++ [below s.sp 96]) s' →
      (∀ k0 text, k0.length = w.H.B → k0.length + text.length < 2 ^ 64 →
        w.ok.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .r5 = BitVec.ofNat 64 (w.H.B + text.length) →
        w.ok.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o w.H.D = hmacBlockKey w.ok.SH.H k0 text) → Q s') :
    WP isa (.call w.finN w.H.finalize) s Q := by
  have hS := w.hS
  have hD := w.hD
  have hB := w.hB
  have hd := w.fin_sd
  refine WP.of_syms (WP.callAny (k := Proof.Hmac.Instance.finalizeScratchContract w.I PPC64LE.abi 96) w.finV.1
    (rd := [⟨ou, w.I.S.stateBytes⟩])
    (wr := [⟨inn, w.I.S.stateBytes⟩, ⟨o, w.I.S.digestBytes⟩, ⟨sc, w.I.scratch * 8⟩]) h.pre
    (by rw [hS, hD]; exact h.hc) (by rw [hS, hD]; exact h.hw) ?_ (by omega_using [hd]))
  intro s' hrd hwr hsp hf hcs hpost sy
  sig_post [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, PPC64LE.abi, PPC64LE.argRegs, stackBelow] at hpost
  simp only [h.r3, h.r4, h.r6, hD, hB] at hpost
  rw [hS, hD] at hf
  rw [w.hIS] at hpost
  exact hQ s' ⟨hrd, hwr, hsp, sy, hcs, Frame.below_mono hf hd (by decide)⟩ hpost

/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem fin_rel {Q : State → State → Prop} {inn ou o sc : Addr}
    (h : ∀ s s', Q s s' → FinArgs w s inn ou o sc ∧ FinArgs w s' inn ou o sc ∧ s.sp = s'.sp ∧
      s.gpr .r5 = s'.gpr .r5) :
    RelCT isa Q (.call w.finN w.H.finalize) fun _ _ => True := by
  have hS := w.hS
  have hD := w.hD
  refine RelCT.call w.finV.1 w.finV.2.1 [⟨ou, w.I.S.stateBytes⟩]
    [⟨inn, w.I.S.stateBytes⟩, ⟨o, w.I.S.digestBytes⟩, ⟨sc, w.I.scratch * 8⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e5⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw, by rw [hS, hD]; exact a'.hc,
    by rw [hS, hD]; exact a'.hw⟩
  sig_pub [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [a.r3, a'.r3, a.r4, a'.r4, a.r6, a'.r6, a.r7, a'.r7, e, e5, and_true]

end

/-! ## The calls through the table -/

open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld)

/-- The load of the address of the table's function `j`, at `tab` (in `t`),
which holds `a`. -/
theorem tload_ok {s : State} {t : Reg} {tab : Addr} {j : Nat} (hj : j < 6) (ht0 : t ≠ .r0)
    (h : s.gpr t = tab) (hin : InRegions (s.rd ++ s.wr) (tab + BitVec.ofNat 64 (8 * j)) 8) {a : Addr}
    (hv : s.mem.readW (tab + BitVec.ofNat 64 (8 * j)) 64 = a) :
    WP isa (.block [.load .d .r12 t (8 * j)]) s fun u => Only [.r12] s u ∧ u.gpr .r12 = a ∧ u.syms = s.syms :=
  WP.of_syms (wp_ld (by rw [h]) hin (fun u o e => WP.block_nil fun sy => ⟨o, by rw [e, hv], sy⟩) ht0
    ⟨by omega_using [hj], by omega_using []⟩)

/-- The table's function `j`, among `ts`, which reaches `n`: the call of `n`
from the state the load of its address leaves. -/
theorem tcall_ok {s : State} {t : Reg} {tab : Addr} {j : Nat} (hj : j < 6) (ht0 : t ≠ .r0)
    (h : s.gpr t = tab) (hin : InRegions (s.rd ++ s.wr) (tab + BitVec.ofNat 64 (8 * j)) 8)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c))
    (hw : s.mem.readW (tab + BitVec.ofNat 64 (8 * j)) 64 = s.syms n) {Q : State → Prop}
    (kk : ∀ s', Only [.r12] s s' → s'.gpr .r12 = s.syms n → s'.syms = s.syms → WP isa (.call n c) s' Q) :
    WP isa (Impl.Hkdf.PPC64LE.tcall t j ts) s Q := by
  unfold Impl.Hkdf.PPC64LE.tcall
  refine WP.seq (WP.mono (tload_ok hj ht0 h hin hw) fun s' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := s'.gpr .r12) rfl ?_ (kk s' o e sy)
  show ts.find? (fun q => s'.syms q.1 == s'.gpr .r12) = _
  rw [e, sy]; exact hf

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

/-- What the load of a table's function's address leaves. -/
abbrev Loaded (Φ : State → Prop) (a : Addr) (u : State) : Prop :=
  ∃ t, Φ t ∧ Only [.r12] t u ∧ u.gpr .r12 = a ∧ u.syms = t.syms

/-- The table's function `j`, among `ts`, which reaches `n` in both runs, at
the same address `a`: two runs of the call of `n` from the states the load of
its address leaves. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {t : Reg} {j : Nat} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} {rs : List Reg} {a : Addr} (hcl : Ck rs (.block [.load .d .r12 t (8 * j)]))
    (hag : ∀ s s', Φ₁ s → Φ₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hld₁ : ∀ s, Φ₁ s → WP isa (.block [.load .d .r12 t (8 * j)]) s fun u =>
      Only [.r12] s u ∧ u.gpr .r12 = a ∧ u.syms = s.syms)
    (hld₂ : ∀ s, Φ₂ s → WP isa (.block [.load .d .r12 t (8 * j)]) s fun u =>
      Only [.r12] s u ∧ u.gpr .r12 = a ∧ u.syms = s.syms)
    (hf₁ : ∀ s, Φ₁ s → ts.find? (fun q => s.syms q.1 == a) = some (n, c))
    (hf₂ : ∀ s, Φ₂ s → ts.find? (fun q => s.syms q.1 == a) = some (n, c))
    (hcall : RelCT isa (fun u u' => Loaded Φ₁ a u ∧ Loaded Φ₂ a u') (.call n c) fun _ _ => True) :
    RelCT isa (fun s s' => Φ₁ s ∧ Φ₂ s') (Impl.Hkdf.PPC64LE.tcall t j ts) fun _ _ => True := by
  unfold Impl.Hkdf.PPC64LE.tcall
  refine (rel_agree (P₁ := Φ₁) (P₂ := Φ₂) (G₁ := Loaded Φ₁ a) (G₂ := Loaded Φ₂ a) hag hcl
    (fun s h => WP.mono (hld₁ s h) fun u ⟨v, e, y⟩ => ⟨s, h, v, e, y⟩)
    (fun s h => WP.mono (hld₂ s h) fun u ⟨v, e, y⟩ => ⟨s, h, v, e, y⟩)).seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun s _ h => by obtain ⟨t, ht, -⟩ := h.1; simp at hf₁; exact hf₁ t ht
  | cons q ts =>
    refine RelCT.icalls_of_call hcall ?_
    rintro u u' ⟨⟨t, h, v, e, y⟩, ⟨t', h', v', e', y'⟩⟩
    refine ⟨a, by show some (u.gpr .r12) = _; rw [e], by show some (u'.gpr .r12) = _; rw [e'],
      ?_, ?_, rfl⟩
    · show (q :: ts).find? (fun q => u.syms q.1 == a) = _
      rw [y]; exact hf₁ t h
    · show (q :: ts).find? (fun q => u'.syms q.1 == a) = _
      rw [y']; exact hf₂ t' h'

/-! ## The stack -/

/-- `B + d` as `(B + e) + (d - e)`. -/
theorem at_off (B : Addr) {d e : Nat} (h : e ≤ d) :
    B + BitVec.ofNat 64 d = B + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) := by
  rw [Offset.add_add, Nat.add_sub_cancel' h]

/-- A region at an offset of a region, for `Covers.of_sub`. -/
theorem sub_at (B : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) :
    ∃ off, B + BitVec.ofNat 64 d = B + BitVec.ofNat 64 e + BitVec.ofNat 64 off ∧ off + n ≤ k :=
  ⟨d - e, at_off B h₁, by omega_using [h₁, h₂]⟩

/-- A region at the base of a region, for `Covers.of_sub`. -/
theorem sub_at0 (B : Addr) {n k : Nat} (h : n ≤ k) :
    ∃ off, B = B + BitVec.ofNat 64 off ∧ off + n ≤ k := ⟨0, (BitVec.add_zero B).symm, by omega_using [h]⟩

/-- The `n` bytes below `L + a`, from `L`. -/
theorem below_off (L : Addr) {a n : Nat} (h : n ≤ a) : below (L + BitVec.ofNat 64 a) n = ⟨L + BitVec.ofNat 64 (a - n), n⟩ := by
  show (⟨L + BitVec.ofNat 64 a - BitVec.ofNat 64 n, n⟩ : Region) = _
  rw [show a = (a - n) + n from (Nat.sub_add_cancel h).symm, ← Offset.add_add, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

/-- The `n` bytes below `L + n`, from `L`. -/
theorem below_at (L : Addr) (n : Nat) : below (L + BitVec.ofNat 64 n) n = ⟨L, n⟩ := by
  show (⟨L + BitVec.ofNat 64 n - BitVec.ofNat 64 n, n⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- `L + d`'s value, without wrapping. -/
theorem toNat_at {L : Addr} {d : Nat} (h : L.toNat + d < 2 ^ 64) : (L + BitVec.ofNat 64 d).toNat = L.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The frame of `F` bytes the body of `.frame (.alloc F) …` runs in, with
`C` bytes of stack below it, from the stack's lowest byte `L`. -/
theorem alloc_at (s : State) {F C : Nat} (h : F + C ≤ s.sp.toNat) :
    s.sp - BitVec.ofNat 64 F = (s.sp - BitVec.ofNat 64 (F + C)) + BitVec.ofNat 64 C ∧
      s.sp = (s.sp - BitVec.ofNat 64 (F + C)) + BitVec.ofNat 64 (F + C) ∧
      (s.sp - BitVec.ofNat 64 (F + C)).toNat + (F + C) ≤ 2 ^ 64 := by
  refine ⟨?_, (BitVec.sub_add_cancel _ _).symm, ?_⟩
  · rw [Offset.sub_ofNat_eq s.sp (show F ≤ F + C by omega_using []), Nat.add_sub_cancel_left]
  · rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, s.sp.isLt])]; exact h),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, s.sp.isLt])]
    omega_using [h, s.sp.isLt]

/-- The memory once a frame of `F` bytes is pushed: the back chain at its
base. -/
theorem alloc_mem (s : State) (F : Nat) :
    Frame [⟨s.sp - BitVec.ofNat 64 F, 8⟩] s.mem (allocated F s).mem :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)

/-- A region apart from the frame's `n` bytes at `p` keeps its bytes. -/
theorem bytes_keep {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame [⟨p, n⟩] m m') {R : Region}
    (hd : R.Disjoint ⟨p, n⟩) (hR : R.len ≤ 2 ^ 64) : bytesAt m' R.base R.len = bytesAt m R.base R.len :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi

/-- Reads registers through register writes (`Only`), deciding which
registers each writes. -/
macro "pupd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- An access within a region at an offset of `L`. -/
theorem in_at (L : Addr) {a d k n : Nat} (rs : List Region) (h₁ : a ≤ d) (h₂ : d + n ≤ a + k)
    (hk : a + k < 2 ^ 64) : InRegions (⟨L + BitVec.ofNat 64 a, k⟩ :: rs) (L + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self, Offset.contains L h₁ h₂ hk⟩

/-- A register write that leaves the callee-saved registers. -/
theorem keep_pres {rs : List Reg} {t t' : State} (K : Keep rs t t') (h : ∀ r ∈ preserved, r ∉ rs := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => K.gpr r (h r hr)

/-- A region holds its first bytes. -/
theorem contains_head {p : Addr} {k n : Nat} (h : n ≤ k) : (⟨p, k⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

/-- An access within the first region. -/
theorem in_head {p : Addr} {k n : Nat} (rs : List Region) (h : n ≤ k) : InRegions (⟨p, k⟩ :: rs) p n :=
  ⟨⟨p, k⟩, List.mem_cons_self, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h⟩

/-- An access at an offset of the first region. -/
theorem in_head_off {p : Addr} {d k n : Nat} (rs : List Region) (h : d + n ≤ k) (hd : d < 2 ^ 64 := by decide) :
    InRegions (⟨p, k⟩ :: rs) (p + BitVec.ofNat 64 d) n :=
  ⟨⟨p, k⟩, List.mem_cons_self, Offset.contains_base _ h hd⟩

/-- HMAC's key, its block size. -/
theorem blockKey_length (w : HVar) (k : List Byte) : (Spec.Hmac.blockKey w.ok.SH.H k).length = w.H.B := by
  have hB := w.ok.hB
  have hDB := w.ok.hDB
  simp only [Spec.Hmac.blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [w.ok.hashLen]; omega_using [hDB]
  · omega_arith

/-- What the functions need of a hash function's sizes: its streaming states
fit their 192 bytes, and the working space of its functions ours. -/
structure HOk (w : HVar) : Prop where
  hS : w.H.S ≤ 192
  hA : w.I.scratch * 8 ≤ Impl.Hkdf.PPC64LE.work
  hW : w.H.W ≤ Impl.Hkdf.PPC64LE.work

instance (w : HVar) : Decidable (HOk w) :=
  decidable_of_iff (w.H.S ≤ 192 ∧ w.I.scratch * 8 ≤ Impl.Hkdf.PPC64LE.work ∧ w.H.W ≤ Impl.Hkdf.PPC64LE.work)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end VG.Proof.Hkdf.PPC64LE

/-! ## `vg_hkdf_key` -/

namespace VG.Proof.Hkdf.PPC64LE

open VG.PPC64LE
open VG.Impl.Hkdf.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HmacTable.PPC64LE (HVar TabOK TabMem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_mov wp_addi wp_addSp wp_ld wp_std wp_mflr wp_mtlr)
open VG.Spec.Hmac (xorPad ipad opad blockKey)
open VG.Spec.Sha256 (bytesAt)

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let key : Region := ⟨s.gpr .r5, 384⟩
    let tab : Region := ⟨s.gpr .r6, 48⟩
    let stk : Region := below s.sp N
    s.rd = [prk, tab] ∧ s.wr = [key] ∧ prk.Disjoint key ∧ tab.Disjoint key ∧
      N ≤ s.sp.toNat ∧ stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 384 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 48 ≤ 2 ^ 64 ∧ TabMem w s.syms (s.gpr .r6) s.mem ∧ TabOK w f s.syms
  post s s' := Spec.Hkdf.Keyed w.ok.SH s'.mem (s.gpr .r5) (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_key` uses: its frame, and below it what HMAC's `init`
uses. -/
def keyStack : Nat := kFr + 144

theorem kFr_eq : kFr = 1920 := rfl
theorem keyStack_eq : keyStack = 2064 := rfl

/-- The state the frame's body starts in, and the regions it names, from the
stack's lowest byte `L`: the 144 bytes `init` uses, then the frame, its
return address at `L + 176` and its working space at `L + 192`. -/
structure KPre (w : HVar) (f : Fns) (s₀ : State) (L : Addr) : Prop where
  sp : s₀.sp = L + BitVec.ofNat 64 144
  nL : L.toNat + keyStack ≤ 2 ^ 64
  rd : s₀.rd = [⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩, ⟨s₀.gpr .r6, 48⟩]
  wr : s₀.wr = [⟨L + BitVec.ofNat 64 176, 1888⟩, ⟨s₀.gpr .r5, 384⟩]
  p_k : Region.Disjoint ⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ ⟨s₀.gpr .r5, 384⟩
  t_k : Region.Disjoint ⟨s₀.gpr .r6, 48⟩ ⟨s₀.gpr .r5, 384⟩
  s_p : Region.Disjoint ⟨L, keyStack⟩ ⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩
  s_k : Region.Disjoint ⟨L, keyStack⟩ ⟨s₀.gpr .r5, 384⟩
  s_t : Region.Disjoint ⟨L, keyStack⟩ ⟨s₀.gpr .r6, 48⟩
  np : (s₀.gpr .r3).toNat + (s₀.gpr .r4).toNat ≤ 2 ^ 64
  nk : (s₀.gpr .r5).toNat + 384 ≤ 2 ^ 64
  nt : (s₀.gpr .r6).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w s₀.syms (s₀.gpr .r6) s₀.mem
  tok : TabOK w f s₀.syms

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem kpre_alloc {s : State} (hp : (keyR w f ns keyStack).pre s) :
    KPre w f (allocated kFr s) (s.sp - BitVec.ofNat 64 keyStack) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  obtain ⟨e₀, -, hn⟩ := alloc_at s (F := kFr) (C := 144) h5
  have hfr : Region.Sub ⟨s.sp - BitVec.ofNat 64 kFr, 8⟩ ⟨s.sp - BitVec.ofNat 64 keyStack, keyStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have hm := alloc_mem s kFr
  refine ⟨e₀, hn, h1, ?_, h3, h4, h6, h7, h8, h9, h10, h11, ?_, h13⟩
  · show (⟨s.sp - BitVec.ofNat 64 kFr + 32, kFr - 32⟩ : Region) :: s.wr = _
    rw [h2, e₀, show (32 : Addr) = BitVec.ofNat 64 32 from rfl, Offset.add_add]; rfl
  · obtain ⟨t0, t1, t2⟩ := h12
    have hd : ∀ o, o + 8 ≤ 48 → ∀ r' ∈ [(⟨s.sp - BitVec.ofNat 64 kFr, 8⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r6, 48⟩ r' := fun o ho r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (h8.sub_left hfr).symm
    refine ⟨?_, ?_, ?_⟩
    · show (allocated kFr s).mem.readW (s.gpr .r6 + BitVec.ofNat 64 0) 64 = s.syms w.initN
      rw [hm.readW (r := ⟨s.gpr .r6, 48⟩) (Offset.contains_base _ (by decide) (by decide))
        (hd 0 (by decide)) (by decide)]; exact t0
    · show (allocated kFr s).mem.readW (s.gpr .r6 + BitVec.ofNat 64 8) 64 = s.syms w.H.updN
      rw [hm.readW (r := ⟨s.gpr .r6, 48⟩) (Offset.contains_base _ (by decide) (by decide))
        (hd 8 (by decide)) (by decide)]; exact t1
    · show (allocated kFr s).mem.readW (s.gpr .r6 + BitVec.ofNat 64 16) 64 = s.syms w.finN
      rw [hm.readW (r := ⟨s.gpr .r6, 48⟩) (Offset.contains_base _ (by decide) (by decide))
        (hd 16 (by decide)) (by decide)]; exact t2

end

/-- After the prologue: the return address saved, the table in `r8`, and
`init`'s arguments in place. -/
structure KA (s₀ : State) (L : Addr) (t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  cs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  r3 : t.gpr .r3 = s₀.gpr .r5
  r4 : t.gpr .r4 = s₀.gpr .r5 + BitVec.ofNat 64 192
  r5 : t.gpr .r5 = s₀.gpr .r3
  r6 : t.gpr .r6 = s₀.gpr .r4
  r7 : t.gpr .r7 = L + BitVec.ofNat 64 192
  r8 : t.gpr .r8 = s₀.gpr .r6
  mem : t.mem = s₀.mem.writeW (L + BitVec.ofNat 64 176) s₀.lr

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : KPre w f s₀ L)
include hp

/-- The prologue. -/
theorem pro_ok : WP isa (.block keyPro) s₀ (KA s₀ L) := by
  unfold keyPro saveLr
  simp only [List.cons_append, List.nil_append]
  refine WP.of_syms (wp_mflr fun s₁ o₁ e₁ => wp_addSp fun s₂ o₂ e₂ => ?_)
  have a₂ : s₂.gpr .r11 + BitVec.ofNat 64 oLr = L + BitVec.ofNat 64 176 := by
    rw [e₂, o₁.sp, hp.sp, BitVec.add_zero, show oLr = 32 from rfl, Offset.add_add]
  refine wp_std a₂ (by rw [o₂.wr, o₁.wr, hp.wr]; exact in_head _ (by decide)) fun s₃ m₃ => ?_
  refine wp_mov fun s₄ o₄ e₄ => wp_mov fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_mov fun s₇ o₇ e₇ =>
    wp_addi (fun s₈ o₈ e₈ => wp_mov fun s₉ o₉ e₉ => wp_mov fun s₁₀ o₁₀ e₁₀ =>
      wp_addSp fun s₁₁ o₁₁ e₁₁ => WP.block_nil fun sy => ?_)
  have K : Keep [.r0, .r11, .r8, .r9, .r10, .r3, .r4, .r5, .r6, .r7] s₀ s₁₁ :=
    (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans (o₇.keep.trans
      (o₈.keep.trans (o₉.keep.trans (o₁₀.keep.trans o₁₁.keep)))))))))).mono
  refine ⟨K.rd, K.wr, K.sp, sy, fun r hr => K.gpr r ((by decide : ∀ r ∈ preserved,
      r ∉ ([.r0, .r11, .r8, .r9, .r10, .r3, .r4, .r5, .r6, .r7] : List Reg)) r hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (pupd_simp [o₁₁.gpr, e₁₁, o₁₀.gpr, e₁₀, o₉.gpr, e₉, o₈.gpr, e₈, o₇.gpr, e₇, o₆.gpr, e₆,
    o₅.gpr, e₅, o₄.gpr, e₄, m₃.gpr, o₂.gpr, e₂, o₁.gpr, e₁]; done)
  · pupd_simp [o₁₁.gpr, e₁₁, o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr, o₄.gpr, m₃.gpr, o₂.gpr, o₁.gpr]
    rw [o₁₀.sp, o₉.sp, o₈.sp, o₇.sp, o₆.sp, o₅.sp, o₄.sp, m₃.sp, o₂.sp, o₁.sp, hp.sp, show kW = 48 from rfl,
      Offset.add_add]
  · rw [o₁₁.mem, o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, m₃.mem, o₂.get .r0, e₁, o₂.mem,
      o₁.mem]

end

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : KPre w f s₀ L)
include hp

/-- The `PRK` the function keys HMAC with. -/
abbrev prkOf (s₀ : State) : List Byte := bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat

/-- After the call of `init`: the states, and what the prologue left. -/
structure KI (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  cs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  svlr : t.mem.readW (L + BitVec.ofNat 64 176) 64 = s₀.lr
  inn : w.ok.SH.Repr t.mem (s₀.gpr .r5) (xorPad (blockKey w.ok.SH.H (prkOf s₀)) ipad)
  out : w.ok.SH.Repr t.mem (s₀.gpr .r5 + BitVec.ofNat 64 192) (xorPad (blockKey w.ok.SH.H (prkOf s₀)) opad)

omit hp in
/-- The return address's slot, in the stack. -/
theorem slot_sub : Region.Sub ⟨L + BitVec.ofNat 64 176, 8⟩ ⟨L, keyStack⟩ := Offset.sub_base _ (by decide)

/-- The table's words, as on entry. -/
theorem tab_word {t : State} (h : KA s₀ L t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (s₀.gpr .r6 + BitVec.ofNat 64 o) 64 = s₀.mem.readW (s₀.gpr .r6 + BitVec.ofNat 64 o) 64 := by
  rw [h.mem]
  exact Mem.readW_writeW_sep (((hp.s_t.sub_left slot_sub).symm).sep
    (Offset.contains_base _ ho (by omega_using [ho])) (Region.contains_self _ _)) (by decide)

end

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : KPre w f s₀ L)
include hp

/-- The load of `init`'s address from the table. -/
theorem tload0 {t : State} (h : KA s₀ L t) :
    WP isa (.block [.load .d .r12 .r8 (8 * 0)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.initN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) h.r8 ⟨⟨s₀.gpr .r6, 48⟩, List.mem_append_left _ (by rw [h.rd, hp.rd]; simp),
      Offset.contains_base _ (by decide) (by decide)⟩
    (by rw [tab_word hp h (by decide)]; exact hp.tmem.1)

omit hp in
/-- The working space, in the stack. -/
theorem sc_sub (hw : HOk w) : Region.Sub ⟨L + BitVec.ofNat 64 192, w.I.scratch * 8⟩ ⟨L, keyStack⟩ :=
  Offset.sub_base _ (by have := hw.hA; simp only [work] at this; rw [keyStack_eq]; omega_using [this])

/-- The stack `init` uses, from `L`. -/
theorem below_t {t : State} (ht : t.sp = s₀.sp) : below t.sp 144 = ⟨L, 144⟩ := by
  rw [ht, hp.sp, below_at]

/-- What the call of `init` needs, once the load of its address wrote `r12`. -/
theorem anyArgs (hw : HOk w) {t t' : State} (h : KA s₀ L t) (o : Only [.r12] t t') :
    AnyArgs w t' (s₀.gpr .r5) (s₀.gpr .r5 + BitVec.ofNat 64 192) (s₀.gpr .r3) (L + BitVec.ofNat 64 192)
      (s₀.gpr .r4).toNat := by
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have nL := hp.nL
  have hK : keyStack = 2064 := rfl
  have nk := hp.nk
  have scS := sc_sub (L := L) hw
  have iS : Region.Sub ⟨s₀.gpr .r5, w.H.S⟩ ⟨s₀.gpr .r5, 384⟩ := Region.sub_prefix (by omega_using [hS])
  have oS : Region.Sub ⟨s₀.gpr .r5 + BitVec.ofNat 64 192, w.H.S⟩ ⟨s₀.gpr .r5, 384⟩ :=
    Offset.sub_base _ (by omega_using [hS])
  have bS : Region.Sub (below t'.sp 144) ⟨L, keyStack⟩ := by
    rw [below_t hp (o.sp.trans h.sp)]; exact Region.sub_prefix (by decide)
  refine ⟨by rw [o.get .r3, h.r3], by rw [o.get .r4, h.r4], by rw [o.get .r5, h.r5], by rw [o.get .r6, h.r6],
    by rw [o.get .r7, h.r7], ?_, Offset.base_disjoint _ (by omega_using [hS]) (by omega_using [hS]),
    hp.p_k.symm.sub_left iS, (hp.s_k.sub_left scS).symm.sub_left iS, hp.p_k.symm.sub_left oS,
    (hp.s_k.sub_left scS).symm.sub_left oS, (hp.s_p.sub_left scS).symm, (hp.s_k.sub_left bS).sub_right iS,
    (hp.s_k.sub_left bS).sub_right oS, hp.s_p.sub_left bS, ?_, by omega_using [nk, hS], ?_, hp.np, ?_, ?_, ?_⟩
  · rw [o.sp, h.sp, hp.sp, toNat_at (by omega_using [nL, hK])]; omega_using []
  · rw [below_t hp (o.sp.trans h.sp)]
    exact Offset.base_disjoint _ (by decide) (by omega_using [hA, hW, nL, hK])
  · rw [toNat_at (by omega_using [nk])]; omega_using [nk, hS]
  · rw [toNat_at (by omega_using [nL, hK])]; omega_using [nL, hK, hA, hW]
  · rw [o.rd, o.wr, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, sub_at0 _ (Nat.le_refl _)⟩
    · exact ⟨⟨s₀.gpr .r5, 384⟩, by simp, sub_at0 _ (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨s₀.gpr .r5, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨L + BitVec.ofNat 64 176, 1888⟩, by simp, sub_at _ (by decide) (by dsimp only; omega_using [hA, hW])⟩
  · rw [o.wr, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨s₀.gpr .r5, 384⟩, by simp, sub_at0 _ (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨s₀.gpr .r5, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨L + BitVec.ofNat 64 176, 1888⟩, by simp, sub_at _ (by decide) (by dsimp only; omega_using [hA, hW])⟩

/-- `PRK` is as on entry, apart from the return address's slot. -/
theorem prk_keep {m : Mem} (hm : m = s₀.mem.writeW (L + BitVec.ofNat 64 176) s₀.lr) :
    bytesAt m (s₀.gpr .r3) (s₀.gpr .r4).toNat = prkOf s₀ := by
  have hf : Frame [⟨L + BitVec.ofNat 64 176, 8⟩] s₀.mem m := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact bytes_keep (R := ⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩) hf (hp.s_p.sub_left slot_sub).symm
    (Nat.le_of_lt (s₀.gpr .r4).isLt)

/-- `init`, called with the table's address in `r12`: the states for `PRK`. -/
theorem init_call (hw : HOk w) {t t' : State} (h : KA s₀ L t) (o : Only [.r12] t t') {Q : State → Prop}
    (hQ : ∀ u, KI w s₀ L u → Q u) : WP isa (.call w.initN w.initC) t' Q := by
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  refine any_call (anyArgs hp hw h o) fun u a hI hO => hQ u ?_
  have scS := sc_sub (L := L) hw
  have fd : ∀ r ∈ ([⟨s₀.gpr .r5, w.H.S⟩, ⟨s₀.gpr .r5 + BitVec.ofNat 64 192, w.H.S⟩,
      ⟨L + BitVec.ofNat 64 192, w.I.scratch * 8⟩] ++ [below t'.sp 144] : List Region),
      Region.Disjoint ⟨L + BitVec.ofNat 64 176, 8⟩ r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.s_k.sub_left slot_sub).sub_right (Region.sub_prefix (by omega_using [hS]))
    · exact (hp.s_k.sub_left slot_sub).sub_right (Offset.sub_base _ (by omega_using [hS]))
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by have := hp.nL; omega_using [this, hA, hW])
    · rw [below_t hp (o.sp.trans h.sp)]
      exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have hm' : t'.mem = s₀.mem.writeW (L + BitVec.ofNat 64 176) s₀.lr := o.mem.trans h.mem
  refine ⟨a.rd.trans (o.rd.trans h.rd), a.wr.trans (o.wr.trans h.wr), a.sp.trans (o.sp.trans h.sp),
    fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [a.cs r hr, o.gpr r (fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr (by decide)),
      h.cs r hr]
  · rw [a.frame.readW (Region.contains_self _ _) fd (by decide), hm', Mem.readW_writeW_self64]
  · rw [← prk_keep hp hm']; exact hI
  · rw [← prk_keep hp hm']; exact hO

/-- `init`, through the table: the states for `PRK`. -/
theorem init_ok (hw : HOk w) {t : State} (h : KA s₀ L t) {Q : State → Prop} (hQ : ∀ u, KI w s₀ L u → Q u) :
    WP isa (tcall .r8 0 f.init) t Q := by
  unfold tcall
  refine WP.seq (WP.mono (tload0 hp h) fun t' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (init_call hp hw h o hQ)
  show f.init.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy, h.sy]; exact hp.tok.i

/-- The epilogue: the return address restored. -/
theorem epi_ok {t : State} (h : KI w s₀ L t) :
    WP isa (.block restoreLr) t fun v => (∀ r ∈ preserved, v.gpr r = s₀.gpr r) ∧ v.sp = s₀.sp ∧
      v.lr = s₀.lr ∧ v.mem = t.mem := by
  unfold restoreLr
  refine wp_addSp fun t₁ o₁ e₁ => ?_
  have a₁ : t₁.gpr .r11 + BitVec.ofNat 64 oLr = L + BitVec.ofNat 64 176 := by
    rw [e₁, h.sp, hp.sp, BitVec.add_zero, show oLr = 32 from rfl, Offset.add_add]
  refine wp_ld a₁ (by rw [o₁.rd, o₁.wr, h.rd, h.wr, hp.wr]; exact InRegions_append_cons.mpr (.inl
      (contains_head (by decide))))
    fun t₂ o₂ e₂ => wp_mtlr fun t₃ g₃ m₃ _ _ sp₃ lr₃ => WP.block_nil ?_
  refine ⟨fun r hr => ?_, by rw [sp₃, o₂.sp, o₁.sp, h.sp], by rw [lr₃, e₂, o₁.mem, h.svlr], by
    rw [m₃, o₂.mem, o₁.mem]⟩
  have n0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr (by decide)
  have n11 : r ∉ [Reg.r11] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr (by decide)
  rw [g₃, o₂.gpr r n0, o₁.gpr r n11, h.cs r hr]

end

/-- What the calling convention keeps, once a frame of `F` bytes is freed. -/
theorem free_abi {s v : State} {F : Nat} (hcs : ∀ r ∈ preserved, v.gpr r = (allocated F s).gpr r)
    (hsp : v.sp = (allocated F s).sp) (hlr : v.lr = (allocated F s).lr) (m : Mem) (u : Nat → BitVec 64) :
    abiPreserved s { freed F v with mem := m, unknowns := u } :=
  ⟨hcs, by show v.sp + BitVec.ofNat 64 F = s.sp; rw [hsp]; exact BitVec.sub_add_cancel _ _, hlr⟩

/-- `vg_hkdf_key`, in its frame. -/
theorem key_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (keyR w f ns keyStack).pre s) :
    WP isa (key f) s fun s' => abiPreserved s s' ∧ (keyR w f ns keyStack).post s s' := by
  have hsp : keyStack ≤ s.sp.toNat := hp.2.2.2.2.1
  have hS := hw.hS
  obtain p := kpre_alloc hp
  obtain ⟨e₀, -, -⟩ := alloc_at s (F := kFr) (C := 144) hsp
  unfold key keyMain
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by rw [keyStack_eq] at hsp; rw [kFr_eq]; omega_using [hsp])
    (WP.seq (WP.mono (pro_ok p) fun t ht => WP.seq (init_ok p hw ht fun u hu =>
      WP.mono (epi_ok p hu) fun v ⟨hcs, hvsp, hlr, hvm⟩ m un fl => ?_)))
  refine ⟨free_abi hcs hvsp hlr m un, ?_⟩
  -- The `free` loses the frame's bytes, which lie apart from `key`.
  have hfs : Region.Sub ⟨s.sp - BitVec.ofNat 64 kFr, kFr⟩ ⟨s.sp - BitVec.ofNat 64 keyStack, keyStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have keep : ∀ o, o + w.H.S ≤ 384 → ∀ i < w.H.S,
      m (s.gpr .r5 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = v.mem (s.gpr .r5 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => lost_byte fl (R := ⟨s.gpr .r5 + BitVec.ofNat 64 o, w.H.S⟩)
      ((p.s_k.sub_left hfs).symm.sub_left (Offset.sub_base _ ho)) hi
  have k0 := keep 0 (by omega_using [hS])
  rw [BitVec.add_zero] at k0
  have hprk : prkOf (allocated kFr s) = bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat :=
    bytes_keep (R := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩) (alloc_mem s kFr)
      (p.s_p.sub_left (by rw [e₀]; exact Offset.sub_base _ (by decide))).symm (Nat.le_of_lt (s.gpr .r4).isLt)
  have hi := hu.inn; have ho := hu.out
  rw [hprk] at hi ho
  exact ⟨w.ok.congr _ _ _ _ (fun i hi => k0 i hi) (by rw [hvm]; exact hi),
    w.ok.congr _ _ _ _ (fun i hi => keep 192 (by omega_using [hS]) i hi) (by rw [hvm]; exact ho)⟩

/-! ## Constant time -/

/-- The taint checks of the pieces of `vg_hkdf_key` between the calls. -/
structure KChecks : Prop where
  pro : Ck [.r3, .r4, .r5, .r6] (.block keyPro)
  tl : Ck [.r8] (.block [.load .d .r12 .r8 (8 * 0)])
  epi : Ck [] (.block restoreLr)

theorem kchecks : KChecks := by
  refine ⟨?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- `vg_hkdf_key` is constant time: two runs whose public data agree leak the
same trace. -/
theorem key_ct {w : HVar} {f : Fns} {ns : List String} (hw : HOk w) (hns : w.initN ∈ ns) :
    ConstantTime isa (keyR w f ns keyStack).pre (keyR w f ns keyStack).pub (key f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := kpre_alloc h; have hp' := kpre_alloc h'
  obtain ⟨qsp, q3, q4, q5, q6, qn⟩ := hpub
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (key f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold key
  refine RelCT.alloc (fun x y ⟨hx, hy⟩ => by rw [hx, hy, qsp]) ((?_ : RelCT isa
    (fun s s' => s = allocated kFr e ∧ s' = allocated kFr e') (keyMain f) fun _ _ => True).mono ?_
    fun _ _ h => h)
  rotate_left
  · rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  rw [qsp] at hp
  have hsp : (allocated kFr e).sp = (allocated kFr e').sp := by simp only [allocated, qsp]
  have hsy : (allocated kFr e).syms w.initN = (allocated kFr e').syms w.initN := qn _ hns
  replace q3 : (allocated kFr e).gpr .r3 = (allocated kFr e').gpr .r3 := q3
  replace q4 : (allocated kFr e).gpr .r4 = (allocated kFr e').gpr .r4 := q4
  replace q5 : (allocated kFr e).gpr .r5 = (allocated kFr e').gpr .r5 := q5
  replace q6 : (allocated kFr e).gpr .r6 = (allocated kFr e').gpr .r6 := q6
  generalize e'.sp - BitVec.ofNat 64 keyStack = L at hp hp'
  generalize allocated kFr e = s₀ at hp hsp hsy q3 q4 q5 q6 ⊢
  generalize allocated kFr e' = s₀' at hp' hsp hsy q3 q4 q5 q6 ⊢
  have kc := kchecks
  unfold keyMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := KA s₀ L) (G₂ := KA s₀' L)
    (rs := [.r3, .r4, .r5, .r6]) (fun s s' hs hs' => by
      subst hs hs'
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [q3, q4, q5, q6]) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => KA s₀ L t ∧ KA s₀' L t') (tcall .r8 0 f.init)
      fun t t' => KI w s₀ L t ∧ KI w s₀' L t' := by
    refine rel_wp (tcall_rel (rs := [.r8]) (a := s₀.syms w.initN) kc.tl (fun t t' k k' => ⟨by rw [k.sp, k'.sp, hsp],
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [k.r8, k'.r8]; exact q6⟩)
      (fun t k => tload0 hp k) (fun t k => by rw [hsy]; exact tload0 hp' k)
      (fun t k => by rw [k.sy]; exact hp.tok.i) (fun t k => by rw [k.sy, hsy]; exact hp'.tok.i) ?_)
      (fun t k => init_ok hp hw k fun _ h => h) (fun t k => init_ok hp' hw k fun _ h => h)
    refine any_rel fun u u' ⟨⟨t, k, o, _, _⟩, ⟨t', k', o', _, _⟩⟩ =>
      ⟨anyArgs hp hw k o, ?_, by rw [o.sp, o'.sp, k.sp, k'.sp, hsp]⟩
    have := anyArgs hp' hw k' o'
    rwa [← q3, ← q4, ← q5] at this
  have r3 := rel_agree (P₁ := KI w s₀ L) (P₂ := KI w s₀' L) (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' k k' => ⟨by rw [k.sp, k'.sp, hsp], fun _ h => absurd h List.not_mem_nil⟩) kc.epi
    (fun t k => WP.mono (epi_ok hp k) fun _ _ => trivial) (fun t k => WP.mono (epi_ok hp' k) fun _ _ => trivial)
  exact ((r1.seq (r2.seq r3)).mono (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.Hkdf.PPC64LE
