module
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls

import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame

/-! # Buffer separation in the complete DSA arithmetic schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem OperandBytes.active {s : State} {B : Addr} {a : Operand} {bs : List Byte}
    (h : OperandBytes s B usedBytes a bs) : OperandBytes s B activeBytes a bs :=
  ⟨h.length, h.source.rd, h.source.val, fun i hi => Nat.le_trans (by decide) (h.source.out i hi)⟩

theorem CallResult.external {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    {a : Operand} {bs : List Byte} (hs : OperandBytes s L.base usedBytes a bs) :
    OperandBytes t L.base usedBytes a bs := by
  refine ⟨(h.fields hd hend a.length).trans hs.length, ?_⟩
  rw [h.pointer hd hend a.pointer]
  have hhi := (side.bounds L).2.2.2.2.1
  have hsep : ∀ i < bs.length, ∀ j < side.length L,
      pointerValue s.mem L.base a.pointer + BitVec.ofNat 64 i ≠ off L.base d + BitVec.ofNat 64 j := by
    intro i hi j hj he
    have hx := hs.source.out i hi
    rw [he, ofs_off L.base (by have := h.ready.scratch.nowrap; omega)] at hx
    omega
  exact callFrame_source h.frame h.keep (by decide) (Nat.le_trans hhi (by decide)) (by decide) hs.source hsep

theorem CallResult.local {L : ExecutionLayout} {side : ModulusSide} {d value e : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    {f : Field} {bs : List Byte} (hs : OperandBytes s L.base activeBytes ⟨.local e, f⟩ bs)
    (he : e + bs.length ≤ usedBytes) (hsep : e + bs.length ≤ d ∨ d + side.length L ≤ e) :
    OperandBytes t L.base activeBytes ⟨.local e, f⟩ bs := by
  apply h.preserve hd hend hs
  intro i hi j hj heq
  change off L.base e + BitVec.ofNat 64 i = off L.base d + BitVec.ofNat 64 j at heq
  have hn := h.ready.scratch.nowrap
  have hx := congrArg (ofs L.base) heq
  rw [ofs_off L.base (by omega), ofs_off L.base (by omega)] at hx
  omega

theorem ExecutionLayout.widths (L : ExecutionLayout) :
    1 ≤ L.qLen ∧ L.qLen ≤ 32 ∧ L.qLen ≤ L.pLen ∧ L.pLen ≤ 384 := by
  rcases L.lengths with ⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide

theorem CallResult.scheduleFrame {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    Outside L.base 128 (usedBytes - 128) s.mem t.mem := by
  have hhi := (side.bounds L).2.2.2.2.1
  have hslot : 136 ≤ slot (side.words L) 8 + tabBytes (side.words L) := by
    unfold slot hdrBytes
    omega
  have hau : activeBytes ≤ usedBytes := by decide
  have hlu : 176 ≤ usedBytes := by decide
  have hla : 128 ≤ activeBytes := by decide
  have ho : 128 ≤ side.offset := by cases side <;> decide
  intro x hx
  apply h.localFrame hend x
  intro range hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only at * <;> omega

end VG.Proof.Dsa.X86_64
