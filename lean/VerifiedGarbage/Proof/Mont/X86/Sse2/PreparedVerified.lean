module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Time
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
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Mont.X86.Sse2.TimeTaint

/-! ### `Mont.X86.Sse2.PreparedABI`, which only this module used -/

section

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

end

end

/-! ### `Mont.X86.Compact.Satisfiable`, which only this module used -/

section

/-! # A concrete i686 state meets the prepared multiplication contract -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satArg (i : Nat) : BitVec 32 :=
  if i = 0 then 0x1000 else if i = 1 then 64 else 1

def satMem : Mem := fun x =>
  if (x - 0x1000).toNat < 512 then
    (satWord ((x - 0x1000).toNat / 8)).extractLsb' (8 * ((x - 0x1000).toNat % 8)) 8
  else if (x - 0x8004).toNat < 20 then
    (satArg ((x - 0x8004).toNat / 4)).extractLsb' (8 * ((x - 0x8004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x8004, 20⟩]
  wr := [⟨0x1000, 512⟩]

end VG.Proof.Mont.X86.Compact

end

end


/-! # `vg_rsa_mont_mul` on x86 with SSE2: verified

The kernel's numbers: `N = 2 w` words of 32 bits, the modulus at array 0,
`-m⁻¹`'s low word at header byte 56, the scratch at array 2 (its `8 N + 28`
bytes run on into array 3), the operands and the result at their arrays.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (Layout Operand wOf arrAt aM)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

/-- What `body preparedParams` takes of a state meeting the contract's precondition. -/
theorem prReady {s : State} (A : PrABI s) :
    Ready preparedParams (wsOf s) (lenOf s) (2 * wOf s.mem (wsOf s)) (arrAt (wOf s.mem (wsOf s)) 2)
      (arrAt (wOf s.mem (wsOf s)) 0) 56 (arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat)
      (arrAt (wOf s.mem (wsOf s)) (arg s 3).toNat) (arrAt (wOf s.mem (wsOf s)) (arg s 4).toNat) s := by
  have Ly := A.lay
  have hinv := Compact.prepared_inverse (by have := A.layout.1; omega_arith) A.inverse
  have hb := A.rightLt
  rw [Compact.numAt_val32, Compact.numAt_val32] at hb
  exact ⟨A.entry, Ly, preparedParams_ok A,
    VG.Proof.Mont.X86.Square.low_inverse s.mem (wsOf s) _ _ Ly.hN hinv, hb⟩

theorem preparedBody_noSp : NoSp (seqs [.block preparedParams, withParams, .block restoreRegs]) :=
  NoSp.of_all (by decide +kernel)

theorem prepared_correct (s : State) (h : (Proof.Rsa.Mont.mulContract abi 56).pre s) :
    ∃ tr t, Exec isa preparedBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.Mont.mulContract abi 56).post s t := by
  have A := prAbi_of h
  have R := prReady A
  obtain ⟨tr, t, E, lt, cong, mem, cs, -, -⟩ := body_ok R.entry R.ly preparedBody_noSp R.par R.inv R.bLt
  have Ly := A.lay
  have hs := Ly.s_le
  have hol := Ly.o_le
  have hst := A.stackBound
  have hb := A.bound
  have po := Compact.operand_apart (w := wOf s.mem (wsOf s)) A.output
  have e2 : arrAt (wOf s.mem (wsOf s)) 2 + 16 * (wOf s.mem (wsOf s) + 2) = arrAt (wOf s.mem (wsOf s)) 4 := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have e3 : arrAt (wOf s.mem (wsOf s)) 3 = arrAt (wOf s.mem (wsOf s)) 2 + 8 * (wOf s.mem (wsOf s) + 2) := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨tr, t, E, ⟨cs, ?_⟩, ?_⟩
  · refine Mem.readW_congr fun i hi => mem _ (fun r hr => ?_) (fun hc => ?_)
    · have := ofs_far (base := wsOf s) (size := lenOf s) (x := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i)
        fun hc => A.retScratch _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega_arith
    · have := (s.gpr .esp).isLt
      simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        at hc
      omega_arith
  · sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [Compact.numAt_val32, Compact.numAt_val32]; exact lt
    · rw [Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32,
        show 64 * wOf s.mem (wsOf s) = 32 * (2 * wOf s.mem (wsOf s)) by omega_arith]
      exact cong
    · intro i hi hj
      apply mem _ (fun r hr => ?_) (fun hc => ?_)
      · rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
          simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by simp only [lenOf] at hb; omega_arith)]]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h2 := hj Proof.Rsa.Mont.aAcc (by simp)
        have h3 := hj Proof.Rsa.Mont.aTmp (by simp)
        have ho := hj (arg s 2).toNat (by simp)
        simp only [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] at h2 h3
        generalize wOf s.mem (wsOf s) = w at *
        have e2' : arrAt w 2 + 16 * (w + 2) = arrAt w 4 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
        have e3' : arrAt w 3 = arrAt w 2 + 8 * (w + 2) := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
        rcases hr with rfl | rfl <;> simp only <;> omega_arith
      · have := (s.gpr .esp).isLt
        have := (arg s 0).isLt
        have := A.stackLo
        refine A.stkScratch (wsOf s + BitVec.ofNat 64 i) ?_ ?_
        · simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            at hc ⊢
          omega_arith
        · simp only [Region.Contains, lenOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat]
          omega_arith

theorem prepared_publicArgs {s t : State} (H : (Proof.Rsa.Mont.mulContract abi 56).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 5, arg s i = arg t i) ∧ wOf s.mem (wsOf s) = wOf t.mem (wsOf t) := by
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_, List.singleton_inj.mp (by with_reducible assumption)⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption

/-- The 24 bytes from `esp` (the return address and the arguments) lie apart
from the registers' frame and the working space. -/
theorem PrABI.argsApart {s : State} (A : PrABI s) :
    ∀ r ∈ (pushed rs4 s).wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 24⟩ r := by
  intro r hr
  rw [pushed_wr, A.wr] at hr
  have := (s.gpr .esp).isLt
  have := A.stackLo
  have := A.stackBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro x hx hf
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, List.length_cons,
      List.length_nil] at hx hf
    omega_arith
  · intro x hx hw
    by_cases h4 : (x - (s.gpr .esp).setWidth 64).toNat < 4
    · exact A.retScratch x (by simp only [Region.Contains]; omega_arith) hw
    · refine A.argScratch x hw ?_
      simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
        BitVec.toNat_ofNat] at hx h4 ⊢
      omega_arith

/-- A byte of the arguments, above the registers' frame. -/
theorem PrABI.argByte {s : State} (A : PrABI s) {k : Nat} (h4 : 4 ≤ k) (hk : k < 24) :
    (pushed rs4 s).mem (X86.Taint.argByte (pushed rs4 s) (16 + k)) =
      (arg s ((k - 4) / 4)).extractLsb' (8 * ((k - 4) % 4)) 8 := by
  have hlo := A.stackLo
  have hhi := A.stackBound
  have e : X86.Taint.argByte (pushed rs4 s) (16 + k) = X86.Taint.argByte s k := by
    simp only [X86.Taint.argByte, pushed_esp]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
      List.length_cons, List.length_nil]
    omega_arith
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [e, F1 _ fun r hr hc => ?_, X86.Taint.argByte_eq (n := 24) (by omega_arith) h4 hk,
    Mem.readW_byte s.mem (argAddr s ((k - 4) / 4)) (Nat.mod_lt _ (by decide))]
  · rfl
  · simp only [List.mem_singleton] at hr; subst hr
    have := (s.gpr .esp).isLt
    simp only [Region.Contains, X86.Taint.argByte, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
      BitVec.toNat_ofNat, List.length_cons, List.length_nil] at hc
    omega_arith

theorem agree_pr {s₁ s₂ : State} (A₁ : PrABI s₁) (A₂ : PrABI s₂) (sp : s₁.gpr .esp = s₂.gpr .esp)
    (args : ∀ i < 5, arg s₁ i = arg s₂ i) : X86.Taint.Agree prTaint (pushed rs4 s₁) (pushed rs4 s₂) := by
  have ab : ∀ {s : State}, PrABI s → X86.Taint.argByte (pushed rs4 s) 16 = (s.gpr .esp).setWidth 64 := by
    intro s A
    have := A.stackLo
    simp only [X86.Taint.argByte, pushed_esp]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
      List.length_cons, List.length_nil]
    omega_arith
  have fit : ∀ {s : State}, PrABI s → ((pushed rs4 s).gpr .esp).toNat + 16 = (s.gpr .esp).toNat := by
    intro s A
    have := A.stackLo
    rw [pushed_esp, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat, List.length_cons, List.length_nil]
    omega_arith
  have wf : ∀ {s : State}, PrABI s → X86.Taint.Wf prTaint (pushed rs4 s) := fun {s} A =>
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨by show _ + 16 + 24 ≤ _; have := fit A; have := A.stackBound; omega_arith,
        by show ∀ r ∈ _, Region.Disjoint ⟨X86.Taint.argByte _ 16, 24⟩ r; rw [ab A]; exact A.argsApart⟩,
      fun _ h => (List.not_mem_nil h).elim, by show _ + 16 < _; have := fit A; have := A.stackBound; omega_arith,
      fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0)⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf A₁, wf A₂,
    X86.Taint.slotsOk_empty, X86.Taint.slotsAgree_empty, fun _ => by rw [pushed_esp, pushed_esp, sp],
    fun k h4 hk => ?_⟩
  · simp only [prTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; rw [pushed_esp, pushed_esp, sp]
  · have hk' : k < 24 := hk
    show (pushed rs4 s₁).mem (X86.Taint.argByte (pushed rs4 s₁) (16 + k)) =
      (pushed rs4 s₂).mem (X86.Taint.argByte (pushed rs4 s₂) (16 + k))
    rw [A₁.argByte h4 hk', A₂.argByte h4 hk', args _ (by omega_arith)]

/-- Two runs with the same numbers and arguments. -/
def PrPair (W : Addr) (L N S mo inv o a b : Nat) (s₁ s₂ : State) : Prop :=
  BPair preparedParams W L N S mo inv o a b s₁ s₂ ∧ PrABI s₁ ∧ PrABI s₂ ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem prepared_constantTime :
    ConstantTime isa (Proof.Rsa.Mont.mulContract abi 56).pre (Proof.Rsa.Mont.mulContract abi 56).pub
      preparedBody := by
  apply RelCT.constantTime
  refine RelCT.mono (P := fun s₁ s₂ => ∃ W L N S mo inv o a b, PrPair W L N S mo inv o a b s₁ s₂)
    (RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => body_relCT (fun _ _ h => h.1) fun x y tx ty x' y' ⟨s₁, s₂, P, ex, ey⟩ e₁ e₂ =>
        ⟨preparedParams_constantTime _ _ _ _ _ _ trivial trivial
          (by rw [ex, ey]; exact agree_pr P.2.1 P.2.2.1 P.1.2.2 P.2.2.2) e₁ e₂, trivial⟩) ?_ fun _ _ _ => trivial
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨sp, args, hw⟩ := prepared_publicArgs hp
  have R := prReady (prAbi_of h₂)
  simp only [wsOf, lenOf, ← args 0 (by decide), ← args 1 (by decide), ← args 2 (by decide),
    ← args 3 (by decide), ← args 4 (by decide)] at R hw
  rw [← hw] at R
  exact ⟨_, _, _, _, _, _, _, _, _, ⟨prReady (prAbi_of h₁), R, sp⟩, prAbi_of h₁, prAbi_of h₂, args⟩

theorem prepared_satisfiable : ∃ s, (Proof.Rsa.Mont.mulContract abi 56).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow]
    [Compact.satState, arg, argAddr, Mem.readW, Mem.read] using Compact.satState

theorem prepared_verified : Verified target preparedBody (Proof.Rsa.Mont.mulContract abi 56) :=
  ⟨prepared_correct, prepared_constantTime, prepared_satisfiable⟩

end VG.Proof.Mont.X86.Sse2
