module

import VerifiedGarbage.Proof.Mont.X86.Sse2.Time
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Body

/-! # `vg_rsa_mont_mul`'s entry

`PrABI s`: the facts of `Proof.Rsa.Mont.mulContract abi 56`'s precondition;
from them, the numbers of the arrays (`w = wOf`, `N = 2 w` words of 32 bits,
the scratch at array 2, which runs on into array 3) and what `body
preparedParams` takes (`prReady`): the arrays' addresses from the header.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (Layout Operand wOf arrAt aM minvWord wordAt)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

structure PrABI (s : State) : Prop where
  stackLo : 56 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 20⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  argScratch : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  stkScratch : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  layout : Layout s.mem (wsOf s) (arg s 1).toNat
  output : Operand (arg s 2).toNat
  left : Operand (arg s 3).toNat
  right : Operand (arg s 4).toNat
  inverse : ((s.mem.readW (wsOf s + BitVec.ofNat 64 (arrAt (wOf s.mem (wsOf s)) aM)) 64).toNat *
      (wordAt s.mem (wsOf s) minvWord).toNat + 1) % 2 ^ 64 = 0
  rightLt : Proof.Rsa.Mont.numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) (arg s 4).toNat <
      Proof.Rsa.Mont.numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) aM

theorem prAbi_of {s : State} (h : (Proof.Rsa.Mont.mulContract abi 56).pre s) : PrABI s := by
  sig_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem PrABI.ws_toNat {s : State} (_ : PrABI s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem PrABI.ws {s : State} (A : PrABI s) : Ws s (wsOf s) (lenOf s) :=
  ⟨by rw [A.wr]; exact List.mem_singleton_self _, by rw [A.ws_toNat]; exact A.bound⟩

theorem PrABI.fit {s : State} (A : PrABI s) : arrAt (wOf s.mem (wsOf s)) 8 ≤ lenOf s := by
  have := A.layout.2.2.1; show _ ≤ (arg s 1).toNat * 8; omega_arith

theorem PrABI.entry {s : State} (A : PrABI s) : Entry s (wsOf s) (lenOf s) := by
  have hlo := A.stackLo
  have hhi := A.stackBound
  refine ⟨hlo, by omega_arith, A.ws, fun j hj => ofs_far fun hc => ?_⟩
  have := (s.gpr .esp).isLt
  by_cases h56 : j < 56
  · refine A.stkScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith
  · refine A.retScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith

theorem PrABI.lay {s : State} (A : PrABI s) :
    Lay (lenOf s) (2 * wOf s.mem (wsOf s)) (arrAt (wOf s.mem (wsOf s)) 2) (arrAt (wOf s.mem (wsOf s)) 0) 56 (arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat) (arrAt (wOf s.mem (wsOf s)) (arg s 3).toNat)
      (arrAt (wOf s.mem (wsOf s)) (arg s 4).toNat) := by
  have fit := A.fit
  have w2 := A.layout.1
  have bnd := A.bound
  have fo := Compact.array_fit fit A.output.1
  have fa := Compact.array_fit fit A.left.1
  have fb := Compact.array_fit fit A.right.1
  have po := Compact.operand_apart (w := wOf s.mem (wsOf s)) A.output
  have pa := Compact.operand_apart (w := wOf s.mem (wsOf s)) A.left
  have pb := Compact.operand_apart (w := wOf s.mem (wsOf s)) A.right
  generalize wOf s.mem (wsOf s) = w at *
  have e0 : arrAt w 0 = 256 := by simp [arrAt, Proof.Rsa.Mont.hdrBytes]
  have e2 : arrAt w 2 = 256 + 16 * (w + 2) := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have e4 : arrAt w 4 = 256 + 32 * (w + 2) := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have e8 : arrAt w 8 = 256 + 64 * (w + 2) := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have l1 : (arg s 1).toNat < 2 ^ 32 := (arg s 1).isLt
  simp only [lenOf] at *
  constructor <;> omega_arith

/-- `w32` of the working space after the registers' push, as on entry. -/
theorem PrABI.pushed_w32 {s : State} (A : PrABI s) {d : Nat} (hd : d + 4 ≤ lenOf s) :
    w32 (pushed rs4 s).mem (wsOf s) d = w32 s.mem (wsOf s) d := by
  have hlo := A.stackLo
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl] at F1
  have := A.bound
  exact Outs.w32 (frame_ws A.entry (c := 0) (n := 16) (by decide) (by decide) (by simpa using F1))
    (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)

/-- The arguments, read from the state after the registers' push. -/
theorem PrABI.readArg {s : State} (A : PrABI s) {t : State} (hesp : t.gpr .esp = s.gpr .esp - 16)
    (hrd : t.rd = s.rd) (hmem : Frame [below (s.gpr .esp) 16] s.mem t.mem) {i : Nat} (hi : i < 5) :
    readSrc t (.mem (prArg i)) = some (arg s i) := by
  have hb := A.stackBound
  have hlo := A.stackLo
  have ea : t.ea (prArg i) = argAddr s i := by
    simp only [State.ea, prArg, at_, hesp, argAddr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (16 : BitVec 32).toNat = 16 from rfl]
    have := (s.gpr .esp).isLt
    omega_arith
  have hin : InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
    rw [hrd, A.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega_arith
  show t.load32 (t.ea (prArg i)) = _
  rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd hin h]
  refine congrArg some (Mem.readW_congr fun j hj => hmem _ fun r hr h => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  have := (s.gpr .esp).isLt
  simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat] at h
  omega_arith

/-- What `preparedParams` keeps of the state after the registers' push. -/
def PrSt (s t : State) : Prop :=
  t.gpr .esp = s.gpr .esp - 16 ∧ t.rd = s.rd ∧ t.mem = (pushed rs4 s).mem ∧ t.wr = (pushed rs4 s).wr

theorem PrSt.upd {s t t' : State} {r : Reg} {v : BitVec 32} (h : PrSt s t) (u : Upd t t' r v) (hr : r ≠ .esp) :
    PrSt s t' :=
  ⟨by rw [u.other _ (Ne.symm hr), h.1], by rw [u.rd, h.2.1], by rw [u.mem, h.2.2.1], by rw [u.wr, h.2.2.2]⟩

theorem PrABI.arg' {s t : State} (A : PrABI s) (h : PrSt s t) {i : Nat} (hi : i < 5) :
    readSrc t (.mem (prArg i)) = some (arg s i) := by
  have hlo := A.stackLo
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl] at F1
  exact A.readArg h.1 h.2.1 (by rw [h.2.2.1]; exact F1) hi

theorem PrSt.ws {s t : State} (A : PrABI s) (h : PrSt s t) : Ws t (wsOf s) (lenOf s) :=
  ⟨by rw [h.2.2.2, pushed_wr]; exact List.mem_cons_of_mem _ A.ws.wr, A.ws.nowrap⟩

/-- The header word `8 + j`'s low half, the address of array `j`. -/
theorem PrABI.header {s t : State} (A : PrABI s) (h : PrSt s t) {r : Reg} {x d j : Nat} (hj : j < 8)
    (hp : PtrAt t (wsOf s) r x) (he : x + d = 64 + 8 * j) :
    ∃ v, readSrc t (.mem (at_ r d)) = some v ∧
      v.toNat = ((wsOf s).toNat + arrAt (wOf s.mem (wsOf s)) j) % 2 ^ 32 := by
  have fit := A.fit
  have := Compact.array_mono (wOf s.mem (wsOf s)) (i := 0) (j := 8) (by decide)
  refine ⟨_, readSrc_ptr (h.ws A) hp (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega_arith), ?_⟩
  show w32 t.mem (wsOf s) (x + d) = _
  rw [h.2.2.1, A.pushed_w32 (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega_arith), he]
  exact Compact.layout_pointer_low A.layout hj

/-- The header word 6's low half, `w`. -/
theorem PrABI.width {s t : State} (A : PrABI s) (h : PrSt s t) {r : Reg} (hp : PtrAt t (wsOf s) r 0) :
    ∃ v, readSrc t (.mem (at_ r 48)) = some v ∧ v.toNat = wOf s.mem (wsOf s) := by
  have fit := A.fit
  have := Compact.array_mono (wOf s.mem (wsOf s)) (i := 0) (j := 8) (by decide)
  have w31 := A.layout.2.1
  refine ⟨_, readSrc_ptr (h.ws A) hp (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega_arith), ?_⟩
  show w32 t.mem (wsOf s) (0 + 48) = _
  rw [h.2.2.1, A.pushed_w32 (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega_arith),
    show 0 + 48 = 8 * Proof.Rsa.Mont.wWord from rfl, Compact.header_low]
  exact Nat.mod_eq_of_lt (by show wOf s.mem (wsOf s) < _; omega_arith)

/-- `prPtr r i`: `r` at array `arg s i`. -/
theorem prPtr_ok {s t : State} (A : PrABI s) (h : PrSt s t) {r : Reg} (hr : r ≠ .esp) (hra : r ≠ .eax)
    {i : Nat} (hi : i < 5) (hix : (arg s i).toNat < 8) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', PrSt s t' →
      (t'.gpr r).toNat = ((wsOf s).toNat + arrAt (wOf s.mem (wsOf s)) (arg s i).toNat) % 2 ^ 32 →
      (∀ q, q ≠ r → q ≠ .eax → t'.gpr q = t.gpr q) → WP isa (.block is) t' Q) :
    WP isa (.block (prPtr r i .eax ++ is)) t Q := by
  simp only [prPtr, List.cons_append, List.nil_append]
  refine wp_movS (A.arg' h (i := 0) (by decide)) fun t1 u1 _ => ?_
  have h1 := h.upd u1 hr
  refine wp_movS (A.arg' h1 hi) fun t2 u2 _ => ?_
  have h2 := h1.upd u2 (by decide)
  refine wp_addS rfl fun t3 u3 _ => ?_
  have h3 := h2.upd u3 (by decide)
  refine wp_addS rfl fun t4 u4 _ => ?_
  have h4 := h3.upd u4 (by decide)
  refine wp_addS rfl fun t5 u5 _ => ?_
  have h5 := h4.upd u5 (by decide)
  refine wp_addS rfl fun t6 u6 _ => ?_
  have h6 := h5.upd u6 hr
  have a5 : (t5.gpr .eax).toNat = 8 * (arg s i).toNat := by
    rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr]
    simp only [BitVec.toNat_add]
    omega_arith
  have r5 : t5.gpr r = arg s 0 := by
    rw [u5.other r hra, u4.other r hra, u3.other r hra, u2.other r hra, u1.gpr]
  have p6 : PtrAt t6 (wsOf s) r (8 * (arg s i).toNat) := by
    rw [PtrAt, u6.gpr, BitVec.toNat_add, r5, a5, A.ws_toNat]
  obtain ⟨v, hv, hvt⟩ := A.header h6 hix p6 (d := 64) (by omega_arith)
  refine wp_movS hv fun t7 u7 _ => k t7 (h6.upd u7 hr) (by rw [u7.gpr]; exact hvt) fun q hq hqa => ?_
  rw [u7.other q hq, u6.other q hq, u5.other q hqa, u4.other q hqa, u3.other q hqa, u2.other q hqa,
    u1.other q hq]

/-- `preparedParams`: the kernel's parameters from the header and the indices. -/
theorem preparedParams_ok {s : State} (A : PrABI s) :
    WP isa (.block preparedParams) (pushed rs4 s)
      (ParamsPost s (wsOf s) (2 * wOf s.mem (wsOf s)) (arrAt (wOf s.mem (wsOf s)) 2)
        (arrAt (wOf s.mem (wsOf s)) 0) 56 (arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat)
        (arrAt (wOf s.mem (wsOf s)) (arg s 3).toNat) (arrAt (wOf s.mem (wsOf s)) (arg s 4).toNat)) := by
  have S0 : PrSt s (pushed rs4 s) := ⟨by rw [pushed_esp]; rfl, pushed_rd _ _, rfl, rfl⟩
  have hW := A.ws_toNat
  have w31 := A.layout.2.1
  simp only [preparedParams, List.append_assoc]
  refine prPtr_ok A S0 (r := .ebp) (by decide) (by decide) (i := 3) (by decide) A.left.1 fun t1 h1 e1 _ => ?_
  refine prPtr_ok A h1 (r := .edi) (by decide) (by decide) (i := 4) (by decide) A.right.1 fun t2 h2 e2 g2 => ?_
  refine prPtr_ok A h2 (r := .edx) (by decide) (by decide) (i := 2) (by decide) A.output.1 fun t3 h3 e3 g3' => ?_
  refine wp_movS (A.arg' h3 (i := 0) (by decide)) fun t4 u4 _ => ?_
  have h4 := h3.upd u4 (by decide)
  have p4 : PtrAt t4 (wsOf s) .ebx 0 := by rw [PtrAt, u4.gpr, hW]; omega_arith
  obtain ⟨v5, hv5, e5⟩ := A.header h4 (j := 0) (by decide) p4 (d := 64) (by omega_arith)
  refine wp_movS hv5 fun t5 u5 _ => ?_
  have h5 := h4.upd u5 (by decide)
  have p5 : PtrAt t5 (wsOf s) .ebx 0 := by rw [PtrAt, u5.other _ (by decide)]; exact p4
  obtain ⟨v6, hv6, e6⟩ := A.header h5 (j := 2) (by decide) p5 (d := 80) (by omega_arith)
  refine wp_movS hv6 fun t6 u6 _ => ?_
  have h6 := h5.upd u6 (by decide)
  have p6 : PtrAt t6 (wsOf s) .ebx 0 := by rw [PtrAt, u6.other _ (by decide)]; exact p5
  obtain ⟨v7, hv7, e7⟩ := A.width h6 p6
  refine wp_movS hv7 fun t7 u7 _ => ?_
  have h7 := h6.upd u7 (by decide)
  refine wp_addS rfl fun t8 u8 _ => wp_addS rfl fun t9 u9 _ => wp_addS rfl fun t10 u10 _ => ?_
  refine wp_addS rfl fun t11 u11 _ => WP.block_nil ?_
  have h11 := (((h7.upd u8 (by decide)).upd u9 (by decide)).upd u10 (by decide)).upd u11 (by decide)
  have g : ∀ q, q ≠ .eax → q ≠ .ebx → t11.gpr q = t6.gpr q := fun q ha hb => by
    rw [u11.other q hb, u10.other q ha, u9.other q ha, u8.other q ha, u7.other q ha]
  have g3 : ∀ q, q ≠ .eax → q ≠ .ebx → q ≠ .esi → q ≠ .ecx → t11.gpr q = t3.gpr q := fun q ha hb hs hc => by
    rw [g q ha hb, u6.other q hc, u5.other q hs, u4.other q hb]
  have fit := A.fit
  have bnd := A.bound
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, lenOf] at fit
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h11.1, h11.2.2.1, h11.2.1, h11.2.2.2⟩
  · show (t11.gpr .ebp).toNat = _
    rw [g3 _ (by decide) (by decide) (by decide) (by decide), g3' .ebp (by decide) (by decide),
      g2 .ebp (by decide) (by decide)]
    exact e1
  · show (t11.gpr .edi).toNat = _
    rw [g3 _ (by decide) (by decide) (by decide) (by decide), g3' .edi (by decide) (by decide)]
    exact e2
  · show (t11.gpr .esi).toNat = _
    rw [g _ (by decide) (by decide), u6.other _ (by decide), u5.gpr, e5]
  · show (t11.gpr .edx).toNat = _
    rw [g3 _ (by decide) (by decide) (by decide) (by decide)]
    exact e3
  · show (t11.gpr .ecx).toNat = _
    rw [g _ (by decide) (by decide), u6.gpr, e6]
  · show (t11.gpr .ebx).toNat = _
    rw [u11.gpr, u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide),
      u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    have h56 : (56 : BitVec 32).toNat = 56 := rfl
    simp only [BitVec.toNat_add, h56, hW]
  · show (t11.gpr .eax).toNat = _
    rw [u11.other _ (by decide), u10.gpr, u9.gpr, u8.gpr, u7.gpr]
    simp only [BitVec.toNat_add, e7]
    omega_arith

end VG.Proof.Mont.X86.Sse2
