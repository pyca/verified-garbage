module

import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Framework.Block

/-! # Range-check timing in the complete DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReadyCheckPublic (side : ModulusSide) where
  layout : ExecutionLayout
  length : Nat
  positive : 1 ≤ length
  fits : (length + 7) / 8 ≤ side.words layout

def ReadyCheckPublic.bytes {side : ModulusSide} (p : ReadyCheckPublic side) (a : Operand) : BPub :=
  ⟨⟨p.layout.base, activeBytes, side.offset, outerWords, side.words p.layout⟩,
    p.layout.pointer a.pointer, p.length⟩

def ReadyCheckPre (side : ModulusSide) (a : Operand) (p : ReadyCheckPublic side) (s : State) : Prop :=
  Ready p.layout s ∧ ∃ bs : List Byte, OperandBytes s p.layout.base activeBytes a bs ∧ bs.length = p.length

theorem checkHead_ok {side : ModulusSide} {a : Operand} {p : ReadyCheckPublic side} {s : State}
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer) (h : ReadyCheckPre side a p s) :
    WP isa (.block (Core.operand arg argLen a ++ Core.enter side.offset)) s (LPre aX arg argLen (p.bytes a)) := by
  obtain ⟨hr, bs, hs, hlen⟩ := h
  obtain ⟨hw2, hw48, hlo, ho, hhi, _⟩ := side.bounds p.layout
  have h256 : 256 ≤ slot outerWords 8 := by decide
  have hactive : activeBytes ≤ 2 ^ 64 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hr.parent (by decide) a ha (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun u ⟨hgu, hua, hul, _, hfu, hku⟩ => ?_
  have child := call_ready (hr.child side) hfu (by decide) (by decide) (by omega) (by omega)
  refine WP.mono (enter_ok hgu child.header hlo hhi ho) fun t ⟨hct, hm, hkt⟩ => ?_
  have hf : Frm p.layout.base (callRanges arg argLen) s.mem t.mem := by rw [hm]; exact hfu
  have hk : Keep coreRegs s t := (hku.trans hkt).mono (by decide)
  refine ⟨side.inverse p.layout, bs, hct, hw2, hw48, ?_, by decide, by decide, by decide,
    ?_, ?_, hlen, ?_, hlen ▸ p.positive, ?_, hlen ▸ p.fits⟩
  · change outerWords < 2 ^ 30; decide
  · change word t.mem p.layout.base (8 * arg) = p.layout.pointer a.pointer
    rw [hm, hua]
    exact hr.publicPointer a.pointer hp
  · change word t.mem p.layout.base (8 * argLen) = BitVec.ofNat 64 bs.length
    rw [hm]
    exact hul.trans hs.length
  · change Src t p.layout.base activeBytes (p.layout.pointer a.pointer) bs
    rw [← hr.publicPointer a.pointer hp]
    exact call_source hf hk (by decide) (by decide) (by decide) hs.source
  · have hfit : (bs.length + 7) / 8 ≤ side.words p.layout := hlen ▸ p.fits
    change side.words p.layout ≤ 48 at hw48
    omega

theorem readyRange_ct (side : ModulusSide) (a : Operand) (aboveOne : Bool)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCheckPre side a)) (Checks.range side.offset a aboveOne) (fun _ _ => True) := by
  unfold Checks.range seqs
  refine RelCT.seq (two_piece (Ψ := fun p s => LPre aX arg argLen (p.bytes a) s) [.x0]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.parent.x0)) hT (fun _ _ h => checkHead_ok ha hp h)) ?_
  refine RelCT.seq (two_map (fun p : ReadyCheckPublic side => p.bytes a) (fun _ _ h => h) loadCheck_ct) ?_
  refine RelCT.seq (loadedRange_ct aboveOne) ?_
  exact two_map (fun p : BPub => p.x) (fun _ _ h => h) leaveAccumulate_ct

theorem readyIsOne_ct (side : ModulusSide) (a : Operand)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCheckPre side a)) (Checks.isOne side.offset a) (fun _ _ => True) := by
  unfold Checks.isOne
  refine RelCT.seq (two_piece (Ψ := fun p s => LPre aX arg argLen (p.bytes a) s) [.x0]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.parent.x0)) hT (fun _ _ h => checkHead_ok ha hp h)) ?_
  refine RelCT.seq (RelCT.seq
    (two_map (fun p : ReadyCheckPublic side => p.bytes a) (fun _ _ h => h) loadCheck_ct) oneMask_ct) ?_
  exact two_map (fun p : BPub => p.x) (fun _ _ h => h) leaveAccumulate_ct

end VG.Proof.Dsa.AArch64
