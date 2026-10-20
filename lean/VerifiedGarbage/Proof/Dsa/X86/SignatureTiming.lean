module

import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
import VerifiedGarbage.Proof.Dsa.X86.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset

/-! # Constant-time release of a complete masked signature -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure SignatureReady (L : CallLayout) (out : BitVec 32) (s : State) : Prop where
  moduli : Moduli L.base L.size L.pLen L.qLen L.p L.q s
  mask : ∃ accepted : Bool, flagW L.base (Layout.field .mask) s = if accepted then BitVec.allOnes 32 else 0
  pointer : pointerValue L.base s (.input .out) = out
  fits : out.toNat + 2 * L.qLen ≤ 2 ^ 32
  write : ∀ e k, e + k ≤ 2 * L.qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 2 * L.qLen⟩

theorem signatureFirst_frame {L : CallLayout} {out : BitVec 32} {s0 : State} (R : SignatureReady L out s0) :
    WP isa (SignVerify.writeScalar L.qLen r false) s0 fun s1 =>
      Scr s1 L.base L.size ∧ pointerValue L.base s1 (.input .out) = out ∧
      OperandReady s1 L.base ((L.qLen + 7) / 8) (.local s) L.qLen := by
  have W := L.lengths
  let n := (L.qLen + 7) / 8
  have N : n ≤ 48 := by dsimp [n]; omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have B := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at B
  have hctx := R.moduli.context N
  have slotSub : Region.Sub ⟨off L.base (slot n 5), 8 * n⟩ ⟨L.base, L.size⟩ := Offset.sub_base L.base (by omega)
  have firstSub : Region.Sub ⟨out.setWidth 64, L.qLen⟩ ⟨out.setWidth 64, 2 * L.qLen⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega : 0 + L.qLen ≤ 2 * L.qLen)
  have A1 := R.apart.sub_right firstSub
  obtain ⟨accepted, mask⟩ := R.mask
  refine WP.mono (writeScalar_ok R.moduli.scr L.saved rfl (by omega) (by omega) L.aligned.2 hctx
    (R.moduli.scalarReady (by decide) N) false accepted mask (by simpa using R.pointer.symm)
    (by have := R.fits; omega) (by intro e k h; exact R.write e k (by omega)) (A1.sub_left slotSub)) fun s1 ⟨_, K, F⟩ => ?_
  have Frame : OutputFrame L.base (out.setWidth 64) (contextBytes n) L.qLen s0.mem s1.mem := F
  have Scr1 := R.moduli.scr.of_keeps K (by decide)
  refine ⟨Scr1, ?_, localReady Scr1 (by omega) (Nat.le_trans (R.moduli.scalarFit (by decide)) L.extent) ?_⟩
  · change s1.mem.readW (off L.base (Layout.field .out)) 32 = out
    rw [Frame.scratch_word A1 (by change contextBytes n ≤ 8224; omega)
      (by have H : 8256 ≤ L.size := L.saved; change 8228 ≤ L.size; omega)
      (by have := R.moduli.scr.nowrap; omega)]
    exact R.pointer
  · change contextBytes n ≤ 14752
    omega

theorem writeSignature_relCT (L : CallLayout) (out : BitVec 32) :
    RelCT isa (fun s t => SignatureReady L out s ∧ SignatureReady L out t)
      (.seq (SignVerify.writeScalar L.qLen r false) (SignVerify.writeScalar L.qLen s true))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have W := L.lengths
  refine RelCT.seq (M := isa) (R := fun s t => Scr s L.base L.size ∧ Scr t L.base L.size ∧
    OperandReady s L.base ((L.qLen + 7) / 8) (.local VG.Impl.Dsa.Layout.s) L.qLen ∧
    OperandReady t L.base ((L.qLen + 7) / 8) (.local VG.Impl.Dsa.Layout.s) L.qLen ∧
    pointerValue L.base s (.input .out) = pointerValue L.base t (.input .out)) ?_
    (writeScalar_relCT L.qLen s true L.base L.size L.saved (by omega) (by omega) L.aligned.2)
  intro s t tr ur sf tf ⟨S, T⟩ E F
  have A := S.moduli.scalarReady (d := r) (by decide) (by omega : (L.qLen + 7) / 8 ≤ 48)
  have B := T.moduli.scalarReady (d := r) (by decide) (by omega : (L.qLen + 7) / 8 ≤ 48)
  have trace := (writeScalar_relCT L.qLen r false L.base L.size L.saved (by omega) (by omega) L.aligned.2
    _ _ _ _ _ _ ⟨S.moduli.scr, T.moduli.scr, A, B, S.pointer.trans T.pointer.symm⟩ E F).1
  obtain ⟨Scr1, P1, R1⟩ := wp_result (signatureFirst_frame S) E
  obtain ⟨Scr2, P2, R2⟩ := wp_result (signatureFirst_frame T) F
  exact ⟨trace, Scr1, Scr2, R1, R2, P1.trans P2.symm⟩

end VG.Proof.Dsa.X86
