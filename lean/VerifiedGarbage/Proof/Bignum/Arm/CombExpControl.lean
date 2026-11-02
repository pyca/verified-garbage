module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel

/-! Only the public remaining row count changes after a comb step. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem Controls.after_counter {base source table : BitVec 32} {bytes N : Nat} {s t : State}
    (h : Controls base source table bytes N s) {value : BitVec 32}
    (mem : t.mem=s.mem.writeW (off (State.addr base) 192) value) :
    Controls base source table bytes N t := by
  have outside := writeW32_outside s.mem (State.addr base) (d:=192) value (by decide)
  rw [←mem] at outside
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [outside_read32 outside (d:=128) (by decide) (by decide)]; exact h.sourcePtr
  · rw [outside_read32 outside (d:=132) (by decide) (by decide)]; exact h.byteCount
  · rw [outside_read32 outside (d:=136) (by decide) (by decide)]; exact h.bitCount
  · rw [outside_read32 outside (d:=204) (by decide) (by decide)]; exact h.spacing
  · rw [outside_read32 outside (d:=232) (by decide) (by decide)]; exact h.tablePtr

theorem next_ok {base source table : BitVec 32} {len w bytes N M g E i : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bytes N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombExp.next) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧ Counter base i t ∧
      t.z=decide (i=0) ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256≤8*len := by
    have arrayFits := h.ready.width ▸ h.ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at arrayFits
    omega
  refine WP.mono (expDecrement_ok s h.ready.workspace (by omega) h.ready.ptr (by omega) fits counter) ?_
  rintro t ⟨mem,flag,rest⟩
  have r : Rest roundClobbers s t := rest.mono (by decide)
  obtain ⟨powerT,frame⟩ := h.after_header (d:=192) (by decide) (by decide) mem rest
    ((rest.gpr .r0 (by decide)).trans h.ready.ptr)
  refine ⟨powerT,A.stable frame r hp,controls.after_counter mem,?_,?_,
    frame.mono (by simpa using A.workspace),r⟩
  · change t.mem.readW (off (State.addr base) 192) 32=BitVec.ofNat 32 i
    rw [mem,Mem.readW_writeW_self32]
    congr 1
  · rw [flag]
    exact decide_eq_decide.mpr (by omega)

theorem round_ok {base source table : BitVec 32} {len w bytes N M g x i : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) (fits : i+1<2^32)
    (h : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x (i+1)) s)
    (hp : P s) (controls : Controls base source table bytes N s) (counter : Counter base (i+1) s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.round K.arithmetic.op) s fun t =>
      Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x i) t ∧ P t ∧
      Controls base source table bytes N t ∧ Counter base i t ∧ t.z=decide (i=0) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.CombExp.round,WP.seq_iff]
  refine WP.mono (row_ok K s hi h hp controls counter) ?_
  rintro u ⟨powerU,pu,controlsU,counterU,frameU,restU⟩
  refine WP.mono (next_ok K.arithmetic u powerU pu controlsU counterU fits) ?_
  rintro t ⟨powerT,pt,controlsT,counterT,flag,frameT,restT⟩
  exact ⟨powerT,pt,controlsT,counterT,flag,frameU.trans frameT,restU.trans restT⟩

end VG.Proof.Bignum.Arm.CombExp
