module

public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Arguments2
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Framework.Block
/-! # Composable streaming-reduction timing steps -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/CallReduceCT.lean`, which only this module imported.
section

/-! # Constant time of the complete parent-to-child reduction call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure CallReducePublic extends ReduceFinishPublic where
  parentInverse : BitVec 64
  extent : pWorkspace ≤ bytes.x.Z
  childLow : slot bytes.x.w 8 ≤ bytes.x.o
  childHigh : bytes.x.o + slot bytes.x.wx 8 + tabBytes bytes.x.wx ≤ bytes.x.Z
  offset : bytes.x.o = qWorkspace
  width48 : bytes.x.wx ≤ 48
  outputPositive : 1 ≤ outputLen
  outputBound : outputLen < 2 ^ 31
  outputWidth : bytes.x.wx = (outputLen + 7) / 8

def CallReducePre (a output : Operand) (p : CallReducePublic) (s : State) : Prop :=
  Good s p.bytes.x.B p.bytes.x.Z p.bytes.x.w p.parentInverse ∧
  ChildReady s.mem p.bytes.x.B p.bytes.x.o p.bytes.x.wx p.modulus p.minv ∧
  (∃ ba : List Byte, OperandBytes s p.bytes.x.B p.bytes.x.Z a ba ∧ ba.length = p.bytes.len) ∧
  pointerValue s.mem p.bytes.x.B a.pointer = p.bytes.ptr ∧
  pointerValue s.mem p.bytes.x.B output.pointer = p.output ∧
  word s.mem p.bytes.x.B output.length.offset = BitVec.ofNat 64 p.outputLen ∧
  (∀ j < p.outputLen, InRegions s.wr (p.output + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.outputLen, p.bytes.x.Z ≤ ofs p.bytes.x.B (p.output + BitVec.ofNat 64 j))

def reduceHead (a output : Operand) : List Instr :=
  Core.operand arg argLen a ++ Core.operand result resultLen output ++ Core.enter qWorkspace

theorem reduceHead_ok {p : CallReducePublic} {s : State} {a output : Operand}
    (ha : pointerFits a.pointer) (ho : pointerFits output.pointer)
    (h : CallReducePre a output p s) :
    WP isa (.block (reduceHead a output)) s (ReduceFinishPre p.toReduceFinishPublic) := by
  obtain ⟨hg, child, ⟨ba, has, hbl⟩, hp, hop, hol, hout, hprefix⟩ := h
  have h256 : 256 ≤ slot p.bytes.x.w 8 := by unfold slot hdrBytes; omega
  have hlo := p.childLow
  have hhi := p.childHigh
  unfold reduceHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments2_ok hg child p.extent (by omega) (by omega) a output ha ho)
    fun u ⟨hgu, hcu, hargs, _, hf, hk⟩ => ?_
  rw [← p.offset]
  refine WP.mono (enter_ok hgu hcu.header p.childLow p.childHigh (by rw [p.offset]; decide))
    fun t ⟨hct, hmem, hkt⟩ => ?_
  have hft : Frm p.bytes.x.B argumentRanges s.mem t.mem := by rw [hmem]; exact hf
  have hkt' : Keep coreRegs s t := (hk.trans hkt).mono (by decide)
  have hargs' : Arguments2 t.mem s.mem p.bytes.x.B a output := hmem ▸ hargs
  have childt : ChildReady t.mem p.bytes.x.B p.bytes.x.o p.bytes.x.wx p.modulus p.minv := hmem ▸ hcu
  refine ⟨⟨⟨⟨hct, ⟨hct.good, childt.modulus, childt.inverse⟩⟩, p.width48⟩,
    ba, hbl, hargs'.1.trans hp, hargs'.2.1.trans has.length, ?_⟩,
    ⟨⟨p.minv, hct, hargs'.2.2.1.trans hop, hargs'.2.2.2.trans hol⟩,
      p.outputPositive, p.outputBound, p.outputWidth, ?_, hprefix⟩⟩
  · rw [← hp]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) has.source
  · intro j hj
    rw [hkt'.wr]
    exact hout j hj

theorem coreReduce_ct (M : Mont) {a output : Operand}
    (ha : pointerFits a.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (reduceHead a output)) hc).isSome = true) :
    RelCT isa (Two (CallReducePre a output)) (Core.reduce M.mm a output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (reduceHead a output))
    (.seq (Arithmetic.reduce M.mm arg argLen) (seqs Core.finish))) _
  refine RelCT.seq (two_piece (Ψ := fun p s => ReduceFinishPre p.toReduceFinishPublic s) [.x0]
    (pins_of (fun p _ => p.bytes.x.B) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.x0)) hT (fun _ _ h => reduceHead_ok ha ho h))
    (two_map CallReducePublic.toReduceFinishPublic (fun _ _ h => h) (reduceFinish_ct M))

end VG.Proof.Dsa.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ReadyReduceCT.lean`, which only this module imported.
section

/-! # Streaming reduction timing in the persistent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReadyReducePublic (d : Nat) where
  layout : ExecutionLayout
  length : Nat
  greater : 255 < layout.subgroup
  odd : layout.subgroup % 2 = 1
  lengthBound : length < 2 ^ 64
  outputStart : activeBytes ≤ d
  outputEnd : d + layout.qLen ≤ usedBytes

def ReadyReducePublic.call {d : Nat} (p : ReadyReducePublic d) (a : Operand) : CallReducePublic where
  bytes := ⟨⟨p.layout.base, activeBytes, qWorkspace, outerWords, p.layout.qWords⟩,
    p.layout.pointer a.pointer, p.length⟩
  minv := p.layout.qInverse
  modulus := p.layout.subgroup
  lower := (ModulusSide.q.bounds p.layout).1
  fits := (ModulusSide.q.bounds p.layout).2.1
  upper := by change outerWords < 2 ^ 30; decide
  greater := by have := p.greater; omega
  odd := p.odd
  greater255 := p.greater
  lengthBound := p.lengthBound
  output := off p.layout.base d
  outputLen := p.layout.qLen
  parentInverse := 0
  extent := by change pWorkspace ≤ activeBytes; decide
  childLow := (ModulusSide.q.bounds p.layout).2.2.1
  childHigh := (ModulusSide.q.bounds p.layout).2.2.2.2.1
  offset := rfl
  width48 := (ModulusSide.q.bounds p.layout).2.1
  outputPositive := (ModulusSide.q.bounds p.layout).2.2.2.2.2.1
  outputBound := (ModulusSide.q.bounds p.layout).2.2.2.2.2.2
  outputWidth := rfl

def ReadyReducePre (d : Nat) (a : Operand) (p : ReadyReducePublic d) (s : State) : Prop :=
  Ready p.layout s ∧ ∃ ba : List Byte, OperandBytes s p.layout.base activeBytes a ba ∧ ba.length = p.length

theorem readyReduce_ct (M : Mont) (d : Nat) (a : Operand)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two (ReadyReducePre d a)) (Core.reduce M.mm a (Core.scalar d)) (fun _ _ => True) := by
  refine two_map (fun p : ReadyReducePublic d => p.call a) ?_ (coreReduce_ct M ha hd hT)
  intro p s ⟨hr, ba, has, hbl⟩
  exact ⟨hr.parent, hr.qChild, ⟨ba, has, hbl⟩, hr.publicPointer a.pointer hpa, rfl,
    hr.length .q, hr.local_write p.outputEnd, hr.local_out p.outputStart p.outputEnd⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScheduleUnaryPre (inputs : SchedulePublic → List (Operand × Nat))
    (a : Operand) (an : SchedulePublic → Nat) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ Available p.layout a (an p) s

def scheduleReducePublic (d : Nat) (an : SchedulePublic → Nat)
    (hal : ∀ p, an p < 2 ^ 64) (hd : activeBytes ≤ d)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    (p : SchedulePublic) : ReadyReducePublic d :=
  ⟨p.layout, an p, p.qGreater, p.qOdd, hal p, hd, hend p⟩

theorem scheduleReduce_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (d : Nat) (a : Operand) (an : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hal : ∀ p, an p < 2 ^ 64)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two (ScheduleUnaryPre inputs a an)) (Core.reduce M.mm a (Core.scalar d))
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .q d s) := by
  refine two_post (two_map (scheduleReducePublic d an hal hd hend) ?_
    (readyReduce_ct M d a ha hpa hd31 hT)) ?_
  · intro p s ⟨hs, ba, has, hbl⟩
    exact ⟨hs.1, ba, has, hbl⟩
  · intro p s ⟨hs, ba, has, hbl⟩
    refine WP.mono (readyReduce_ok M hs.1 p.qGreater p.qOdd a ha has (hbl ▸ hal p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega)) p.qFits

theorem CallResult.keepReduced {L : ExecutionLayout} {side other : ModulusSide}
    {d value e : Nat} {s t : State} (h : CallResult L side d value s t) (hs : Ready L s)
    (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    (he : activeBytes ≤ e) (hee : e + other.length L ≤ usedBytes)
    (hsep : e + other.length L ≤ d ∨ d + side.length L ≤ e)
    (hr : LocalReduced L other e s) : LocalReduced L other e t := by
  have hbs := hs.readLocal other e he hee
  have hlen : (Spec.Rsa.bytesAt s.mem (off L.base e) (other.length L)).length = other.length L := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have ht := h.local hd hend hbs (by rw [hlen]; exact hee) (by rw [hlen]; exact hsep)
  have htbytes := operand_bytesAt ht
  simp only [hlen] at htbytes
  change Spec.Rsa.bytesAt t.mem (off L.base e) (other.length L) = _ at htbytes
  unfold LocalReduced
  rw [htbytes]
  exact hr

theorem scheduleReduceKeep_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (d e : Nat) (a : Operand) (an : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hal : ∀ p, an p < 2 ^ 64)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    (he : activeBytes ≤ e) (hee : ∀ p : SchedulePublic, e + p.layout.qLen ≤ usedBytes)
    (hsep : ∀ p : SchedulePublic, e + p.layout.qLen ≤ d ∨ d + p.layout.qLen ≤ e)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two fun p s => ScheduleUnaryPre inputs a an p s ∧ LocalReduced p.layout .q e s)
      (Core.reduce M.mm a (Core.scalar d))
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .q d s ∧ LocalReduced p.layout .q e s) := by
  refine two_post (two_map (scheduleReducePublic d an hal hd hend) ?_
    (readyReduce_ct M d a ha hpa hd31 hT)) ?_
  · intro p s ⟨⟨hs, ba, has, hbl⟩, hr⟩
    exact ⟨hs.1, ba, has, hbl⟩
  · intro p s ⟨⟨hs, ba, has, hbl⟩, hr⟩
    refine WP.mono (readyReduce_ok M hs.1 p.qGreater p.qOdd a ha has (hbl ▸ hal p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_, ?_⟩
    · exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega)) p.qFits
    · exact h.keepReduced hs.1 hd (hend p) he (hee p) (hsep p) hr

end VG.Proof.Dsa.AArch64
