module

import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
public import VerifiedGarbage.Proof.Dsa.AArch64.Product
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
meta import VerifiedGarbage.Proof.Dsa.AArch64.Product
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call
meta import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! ### `Dsa.AArch64.ScheduleCheckCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ScheduleCallCT`, which this module and modules that import it used -/

section

/-! # Composable timing steps for complete DSA arithmetic schedules -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScheduleBinaryPre (inputs : SchedulePublic → List (Operand × Nat))
    (a b : Operand) (an bn : SchedulePublic → Nat) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ Available p.layout a (an p) s ∧ Available p.layout b (bn p) s

def scheduleCallPublic (side : ModulusSide) (d : Nat) (an bn : SchedulePublic → Nat)
    (ha1 : ∀ p, 1 ≤ an p) (haw : ∀ p, (an p + 7) / 8 ≤ side.words p.layout)
    (hb1 : ∀ p, 1 ≤ bn p) (hb1024 : ∀ p, bn p ≤ 1024)
    (hd : activeBytes ≤ d) (hend : ∀ p : SchedulePublic, d + side.length p.layout ≤ usedBytes)
    (p : SchedulePublic) : ReadyCallPublic side d :=
  ⟨p.layout, an p, bn p, p.greater side, p.odd side, ha1 p, haw p, hb1 p, hb1024 p, hd, hend p⟩

theorem schedulePow_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (side : ModulusSide) (d : Nat) (a b : Operand) (an bn : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (ha1 : ∀ p, 1 ≤ an p) (haw : ∀ p, (an p + 7) / 8 ≤ side.words p.layout)
    (hb1 : ∀ p, 1 ≤ bn p) (hb1024 : ∀ p, bn p ≤ 1024)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16) (hend : ∀ p : SchedulePublic, d + side.length p.layout ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ScheduleBinaryPre inputs a b an bn))
      (Core.pow M.mm side.offset a b ⟨.local d, side.lengthField⟩)
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout side d s) := by
  refine two_post (two_map (scheduleCallPublic side d an bn ha1 haw hb1 hb1024 hd hend) ?_
    (readyPow_ct M side d a b ha hb hpa hpb hd31 hT)) ?_
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    exact ⟨hs.1, ba, bb, has, hbs, hbl, hel⟩
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    refine WP.mono (readyPow_ok M hs.1 side (p.greater side) (p.odd side) a b ha hb has hbs
      (hbl ▸ ha1 p) (hbl ▸ haw p) (hel ▸ hb1 p) (hel ▸ hb1024 p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (VG.Proof.Dsa.powMod_lt _ _ (by have := p.greater side; omega_using [this])) (p.fits side)

theorem scheduleProduct_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (side : ModulusSide) (d : Nat) (a b : Operand) (an bn : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (ha1 : ∀ p, 1 ≤ an p) (haw : ∀ p, (an p + 7) / 8 ≤ side.words p.layout)
    (hb1 : ∀ p, 1 ≤ bn p) (hbw : ∀ p, (bn p + 7) / 8 ≤ side.words p.layout)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16) (hend : ∀ p : SchedulePublic, d + side.length p.layout ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ScheduleBinaryPre inputs a b an bn))
      (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩)
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout side d s) := by
  have hb1024 (p : SchedulePublic) : bn p ≤ 1024 := by
    have := hbw p
    have := (side.bounds p.layout).2.1
    change side.words p.layout ≤ 48 at this
    omega_arith
  let pub (p : SchedulePublic) : ReadyProductPublic side d :=
    { scheduleCallPublic side d an bn ha1 haw hb1 hb1024 hd hend p with secondFits := hbw p }
  refine two_post (two_map pub ?_ (readyProduct_ct M side d a b ha hb hpa hpb hd31 hT)) ?_
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    exact ⟨hs.1, ba, bb, has, hbs, hbl, hel⟩
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    refine WP.mono (readyProduct_ok M hs.1 side (p.greater side) (p.odd side) a b ha hb has hbs
      (hbl ▸ ha1 p) (hbl ▸ haw p) (hel ▸ hb1 p) (hel ▸ hbw p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have := p.greater side; omega_using [this])) (p.fits side)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ScheduleReduceCT`, which this module and modules that import it used -/

section

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
  have h256 : 256 ≤ slot p.bytes.x.w 8 := by unfold slot hdrBytes; omega_using []
  have hlo := p.childLow
  have hhi := p.childHigh
  unfold reduceHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments2_ok hg child p.extent (by omega_using [h256, hlo]) (by omega_using [hhi]) a output ha ho)
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
  greater := by have := p.greater; omega_using [this]
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
    exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega_using [this])) p.qFits

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
    · exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega_using [this])) p.qFits
    · exact h.keepReduced hs.1 hd (hend p) he (hee p) (hsep p) hr

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.EqualCT`, which only this module used -/

section

/-! # Constant-time equality of DSA byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure EqualPublic where
  base : Addr
  left : Addr
  right : Addr
  length : Nat

def EqualPre (a b : Operand) (p : EqualPublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .x0 = p.base ∧
    pointerValue s.mem p.base a.pointer = p.left ∧ pointerValue s.mem p.base b.pointer = p.right ∧
    word s.mem p.base a.length.offset = BitVec.ofNat 64 p.length

def EqualRegs (p : EqualPublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.left ∧ s.gpr .x2 = p.right ∧
    s.gpr .x9 = BitVec.ofNat 64 p.length

/-- The equality check and mask accumulation depend only on the public
workspace address, operand pointers and length. Input contents remain secret. -/
theorem equal_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (unequal : Bool) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
      ([mov .x2 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EqualPre a b)) (Checks.equal a b unequal) (fun _ _ => True) := by
  unfold Checks.equal seqs
  refine RelCT.seq (two_piece (Ψ := EqualRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hleft, hright, hlen⟩
    exact WP.mono (equalHead_ok hs hdi hZ a b ha hb) fun t h =>
      ⟨(h.2.2.2.2.2.gpr .x0 (by decide)).trans hdi, h.1.trans hleft,
        h.2.1.trans hright, h.2.2.1.trans hlen⟩
  have hp : Pins EqualRegs [.x0, .x1, .x2, .x9] :=
    pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.left
      else if r = .x2 then p.right else BitVec.ofNat 64 p.length) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2)
  cases unequal <;> exact two_taint [.x0, .x1, .x2, .x9] hp (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ZeroCT`, which only this module used -/

section

/-! # Constant-time zero checks of DSA byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ZeroPublic where
  base : Addr
  left : Addr
  length : Nat

def ZeroPre (a : Operand) (p : ZeroPublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .x0 = p.base ∧
    pointerValue s.mem p.base a.pointer = p.left ∧
    word s.mem p.base a.length.offset = BitVec.ofNat 64 p.length

def ZeroRegs (p : ZeroPublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.left ∧
    s.gpr .x9 = BitVec.ofNat 64 p.length

/-- The zero check and mask accumulation depend only on the public
workspace address, operand pointers and length. Input contents remain secret. -/
theorem zero_ct {a : Operand} (ha : pointerFits a.pointer)
    (nonzero : Bool) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ZeroPre a)) (Checks.zero a nonzero) (fun _ _ => True) := by
  unfold Checks.zero seqs
  refine RelCT.seq (two_piece (Ψ := ZeroRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hleft, hlen⟩
    exact WP.mono (zeroHead_ok hs hdi hZ a ha) fun t h =>
      ⟨(h.2.2.2.2.gpr .x0 (by decide)).trans hdi, h.1.trans hleft,
        h.2.1.trans hlen⟩
  have hp : Pins ZeroRegs [.x0, .x1, .x9] :=
    pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.left
      else BitVec.ofNat 64 p.length) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)
  cases nonzero <;> exact two_taint [.x0, .x1, .x9] hp (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.MinusCT`, which only this module used -/

section

/-! # Timing of modulus-minus constants used in DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def MinusRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x14 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aN) ∧ s.gpr .x17 = off L.B (slot L.w aY)

theorem pins_minusRegs : Pins MinusRegs [.x14, .x16, .x17] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else if r = .x16 then off L.B (slot L.w aN)
    else off L.B (slot L.w aY)) (by
      intro L s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)

def minusRest (amount : Nat) : Prog isa :=
  .seq (.block ([movi .x4 amount, movi .x7 0, ld .x3 .x16, .subs .x .x3 .x3 .x4,
      st .x3 .x17, next .x16, next .x17, .subImm .x .x14 .x14 1] : List Instr)) (countLoop .x14 minusTail)

theorem minusCore_ct (amount : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) hc).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) (fun _ _ => True) := by
  apply fuseBlocks_ct (a := [ldh .x14 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY)])
  refine RelCT.seq (two_piece (Ψ := MinusRegs) [.x0]
    (pins_of (fun L _ => L.B) (by
      intro L s ⟨_, hg, _⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hg.x0)) (by taint_decide) ?_)
    (two_taint [.x14, .x16, .x17] pins_minusRegs hT)
  intro L s ⟨minv, hg, hz⟩
  brun [MinusRegs, hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
    hdr_enc (show sArr aY < 32 by decide), hg.ld hz (show sW < 32 by decide),
    hg.ld hz (show sArr aN < 32 by decide), hg.ld hz (show sArr aY < 32 by decide),
    hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide)]

structure MinusPublic (amount : Nat) extends BPub where
  minv : BitVec 64
  modulus : Nat
  lower : 2 ≤ x.wx
  upper : x.wx < 2 ^ 31
  enough : amount ≤ modulus

def MinusPre {amount : Nat} (p : MinusPublic amount) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  ModCtx s (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧ FinishPre p.toBPub s

theorem minusFinish_ct (amount : Nat) (ha : amount < 2 ^ 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) hc).isSome = true) :
    RelCT isa (Two (@MinusPre amount))
      (.seq (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.toBPub s)
    (two_map (fun p : MinusPublic amount => p.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩) (minusCore_ct amount hT)) ?_)
    (two_map MinusPublic.toBPub (fun _ _ h => h) finish_ct)
  intro p s ⟨hc, hm, hf⟩
  exact WP.mono (minus_ok hc hm p.lower p.upper ha p.enough)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ReadyRangeCT`, which only this module used -/

section

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
  have child := call_ready (hr.child side) hfu (by decide) (by decide) (by omega_using [hlo, h256]) (by omega_using [hhi, hactive])
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
    omega_using [hfit, hw48]

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

end

end

/-! ### `Dsa.AArch64.ReadyByteChecksCT`, which only this module used -/

section

/-! # Byte validation timing from the persistent public field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG.Impl.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem readyZero_ct {a : Operand} (ha : pointerFits a.pointer)
    (hp : stablePointer a.pointer) (hl : a.length ≠ .mask) (nonzero : Bool)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.zero a nonzero) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, (L.fields a.length).toNat⟩ : ZeroPublic)) ?_ (zero_ct ha nonzero hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.x0, h.publicPointer a.pointer hp, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

theorem readyEqual_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hl : a.length ≠ .mask) (unequal : Bool)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
      ([mov .x2 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.equal a b unequal) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, L.pointer b.pointer, (L.fields a.length).toNat⟩ : EqualPublic)) ?_
    (equal_ct ha hb unequal hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.x0,
    h.publicPointer a.pointer hpa, h.publicPointer b.pointer hpb, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ReadyMinusCT`, which only this module used -/

section

/-! # Constant-time construction of p-minus-one and q-minus-two -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReadyMinusPublic (side : ModulusSide) (amount d : Nat) where
  layout : ExecutionLayout
  enough : amount ≤ side.value layout
  outputStart : activeBytes ≤ d
  outputEnd : d + side.length layout ≤ usedBytes

def ReadyMinusPublic.call {side : ModulusSide} {amount d : Nat} (p : ReadyMinusPublic side amount d) : MinusPublic amount where
  x := ⟨p.layout.base, activeBytes, side.offset, outerWords, side.words p.layout⟩
  ptr := off p.layout.base d
  len := side.length p.layout
  minv := side.inverse p.layout
  modulus := side.value p.layout
  lower := (side.bounds p.layout).1
  upper := by
    change side.words p.layout < 2 ^ 31
    have h : side.words p.layout ≤ 48 := (side.bounds p.layout).2.1
    omega_using [h]
  enough := p.enough

theorem minusCallHead_ok {side : ModulusSide} {amount d : Nat} {p : ReadyMinusPublic side amount d}
    {s : State} (hd31 : d < 2 ^ 16) (hr : Ready p.layout s) :
    WP isa (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) s
      (MinusPre p.call) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds p.layout
  have h256 : 256 ≤ slot outerWords 8 := by decide
  have hactive : activeBytes ≤ 2 ^ 64 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hr.parent (by decide) ⟨.local d, side.lengthField⟩ hd31 (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun u ⟨hgu, hup, hul, _, hfu, hku⟩ => ?_
  have child := call_ready (hr.child side) hfu (by decide) (by decide) (by omega_using [hlo, h256]) (by omega_using [hhi, hactive])
  refine WP.mono (enter_ok hgu child.header hlo hhi ho) fun t ⟨hct, hm, hkt⟩ => ?_
  have hk : Keep coreRegs s t := (hku.trans hkt).mono (by decide)
  refine ⟨hct, ⟨hct.good, hm ▸ child.modulus, hm ▸ child.inverse⟩,
    ⟨⟨side.inverse p.layout, hct, ?_, ?_⟩, hk1, hk31, rfl, ?_, hr.local_out p.outputStart p.outputEnd⟩⟩
  · change word t.mem p.layout.base (8 * result) = off p.layout.base d
    rw [hm]
    exact hup
  · change word t.mem p.layout.base (8 * resultLen) = BitVec.ofNat 64 (side.length p.layout)
    rw [hm]
    exact hul.trans (hr.length side)
  · intro j hj
    rw [hk.wr]
    exact hr.local_write p.outputEnd j hj

theorem readyMinus_ct (side : ModulusSide) (amount d : Nat)
    (ha : amount < 2 ^ 16) (hd31 : d < 2 ^ 16)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) h₂).isSome = true) :
    RelCT isa (Two fun p : ReadyMinusPublic side amount d => Ready p.layout)
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  unfold Checks.modulusMinus
  refine RelCT.seq (two_piece (Ψ := fun p s => MinusPre p.call s) [.x0]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.parent.x0)) ht₁ (fun _ _ h => minusCallHead_ok hd31 h)) ?_
  exact (two_map ReadyMinusPublic.call (fun _ _ h => h) (minusFinish_ct amount ha ht₂))

end VG.Proof.Dsa.AArch64

end

end

/-! # Validation timing steps that preserve the complete schedule state -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem CheckEffect.schedule {inputs : SchedulePublic → List (Operand × Nat)} {p : SchedulePublic}
    {valid : Bool} {s t : State} (h : CheckEffect p.layout valid s t) (hs : ScheduleState inputs p s)
    (stable : ∀ a ∈ inputs p, a.1.length ≠ .mask ∧ stablePointer a.1.pointer) : ScheduleState inputs p t := by
  refine ⟨h.ready, ?_, valid, h.mask⟩
  intro a ha
  obtain ⟨bs, hb, hlen⟩ := hs.2.1 a ha
  obtain ⟨hf, hp⟩ := stable a ha
  exact ⟨bs, h.preserve hs.1 (by decide) hf hp hb, hlen⟩

theorem scheduleRange_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (side : ModulusSide) (a : Operand) (an : SchedulePublic → Nat) (aboveOne : Bool)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    (h1 : ∀ p, 1 ≤ an p) (hw : ∀ p, (an p + 7) / 8 ≤ side.words p.layout)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ScheduleUnaryPre inputs a an)) (Checks.range side.offset a aboveOne)
      (Two (ScheduleState inputs)) := by
  refine two_post (two_map (fun p : SchedulePublic => (⟨p.layout, an p, h1 p, hw p⟩ : ReadyCheckPublic side))
    (fun p s ⟨hs, hbs⟩ => ⟨hs.1, hbs⟩) (readyRange_ct side a aboveOne ha hp hT)) ?_
  intro p s ⟨hs, bs, hbs, hlen⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  exact WP.mono (readyRange_ok hs.1 side a ha hbs (hlen ▸ h1 p) (hlen ▸ hw p) aboveOne hm)
    fun t h => h.schedule hs (stable p)

theorem scheduleIsOne_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (side : ModulusSide) (a : Operand) (an : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    (h1 : ∀ p, 1 ≤ an p) (hw : ∀ p, (an p + 7) / 8 ≤ side.words p.layout)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ScheduleUnaryPre inputs a an)) (Checks.isOne side.offset a)
      (Two (ScheduleState inputs)) := by
  refine two_post (two_map (fun p : SchedulePublic => (⟨p.layout, an p, h1 p, hw p⟩ : ReadyCheckPublic side))
    (fun p s ⟨hs, hbs⟩ => ⟨hs.1, hbs⟩) (readyIsOne_ct side a ha hp hT)) ?_
  intro p s ⟨hs, bs, hbs, hlen⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  exact WP.mono (readyIsOne_ok hs.1 side a ha hbs (hlen ▸ h1 p) (hlen ▸ hw p) hm)
    fun t h => h.schedule hs (stable p)

theorem scheduleZero_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a : Operand) (an : SchedulePublic → Nat) (nonzero : Bool)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer) (hl : a.length ≠ .mask)
    (h1 : ∀ p, 1 ≤ an p) (h64 : ∀ p, an p < 2 ^ 64)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ScheduleUnaryPre inputs a an)) (Checks.zero a nonzero)
      (Two (ScheduleState inputs)) := by
  refine two_post (two_map SchedulePublic.layout (fun _ _ h => h.1.1) (readyZero_ct ha hp hl nonzero hT)) ?_
  intro p s ⟨hs, bs, hbs, hlen⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  exact WP.mono (readyZero_ok hs.1 a ha hbs (hlen ▸ h1 p) (hlen ▸ h64 p) nonzero hm)
    fun t h => h.schedule hs (stable p)

theorem scheduleEqual_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a b : Operand) (an : SchedulePublic → Nat) (unequal : Bool)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hl : a.length ≠ .mask)
    (h1 : ∀ p, 1 ≤ an p) (h64 : ∀ p, an p < 2 ^ 64)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
      ([mov .x2 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ScheduleBinaryPre inputs a b an an)) (Checks.equal a b unequal)
      (Two (ScheduleState inputs)) := by
  refine two_post (two_map SchedulePublic.layout (fun _ _ h => h.1.1)
    (readyEqual_ct ha hb hpa hpb hl unequal hT)) ?_
  intro p s ⟨hs, ⟨as, has, hal⟩, ⟨bs, hbs, hbl⟩⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  exact WP.mono (readyEqual_ok hs.1 a b ha hb has hbs (hal.trans hbl.symm)
    (hal ▸ h1 p) (hal ▸ h64 p) unequal hm) fun t h => h.schedule hs (stable p)

theorem scheduleMinus_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (side : ModulusSide) (amount d : Nat) (ha : amount < 2 ^ 16)
    (ham : ∀ p : SchedulePublic, amount ≤ side.value p.layout)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16)
    (hend : ∀ p : SchedulePublic, d + side.length p.layout ≤ usedBytes)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) h₂).isSome = true) :
    RelCT isa (Two (ScheduleState inputs))
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (Two (ScheduleState inputs)) := by
  refine two_post (two_map (fun p : SchedulePublic =>
    (⟨p.layout, ham p, hd, hend p⟩ : ReadyMinusPublic side amount d))
    (fun _ _ h => h.1) (readyMinus_ct side amount d ha hd31 ht₁ ht₂)) ?_
  intro p s hs
  exact WP.mono (readyMinus_ok hs.1 side amount ha (ham p) d hd (hend p))
    fun t h => h.schedule hs hd (hend p) (stable p)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.PublicScheduleCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.PublicPrefix`, which only this module used -/

section

/-! # DSA validation before the public subgroup exponentiations -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem publicPrefix_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs (Checks.publicPrefix M.mm)) s0 fun s6 =>
      Ready L s6 ∧ (∃ v : Bool, word s6.mem L.base Field.mask.offset = mask v) ∧
      OperandBytes s6 L.base usedBytes ⟨.input .q, .qLen⟩ qb ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s6.mem ∧ Keep coreRegs s0 s6 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 16; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_
  have hq6 := h6.external (by decide) hqm hq5
  have hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  exact ⟨h6.ready, ⟨_, hm6⟩, hq6,
    (((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans (h6.scheduleFrame (by decide) hqm)),
    (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of DSA domain and public-key validation -/

/-! # Preserving the public subgroup order through DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The input q is the public subgroup order, including its allocated width. -/
def PublicKeyPre (inputs : SchedulePublic → List (Operand × Nat)) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ ∃ qb : List Byte,
    OperandBytes s p.layout.base usedBytes ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem publicPrefix_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega_using [this]
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .p Core.generator (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.generator]) (by simp [stablePointer, Core.generator]) pp pf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .p Core.publicValue (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.publicValue]) (by simp [stablePointer, Core.publicValue]) pp pf (by taint_decide)
  have h3 := scheduleMinus_ct inputs stable .p 1 t (by decide)
    (fun p => Nat.le_of_lt p.pGreater) (by decide) (by decide) (element_space (by decide))
    (by taint_decide) (by taint_decide)
  have h4 := scheduleReduce_ct M inputs stable u (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleZero_ct inputs stable (Core.scalar u) (fun p => p.layout.qLen) false
    (by change u < 2 ^ 16; decide) (by simp [stablePointer, Core.scalar]) (by decide)
    qp (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  have h6 := scheduleMinus_ct inputs stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  unfold Checks.publicPrefix seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hg p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hy p)).active⟩) h2) ?_
  refine RelCT.seq h3 ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, h.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q u (by decide) (scalar_space (by decide) p)⟩) h5) ?_
  exact h6

theorem publicPrefix_known_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (PublicKeyPre inputs)) := by
  refine two_post (two_map (fun p => p) (fun _ _ h => h.1) ((publicPrefix_ct M inputs stable hg hy).mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨gb, hgb, hgl⟩ := hs.2.1 _ (hg p)
  obtain ⟨yb, hyb, hyl⟩ := hs.2.1 _ (hy p)
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (publicPrefix_ok M hs.1 p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    hgb hyb hqb hgl hyl hm) fun t ⟨hr, hmask, hq, hf, hk⟩ => ?_
  refine ⟨⟨hr, ?_, hmask⟩, qb, hq, hql, hqv⟩
  intro a ha
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 a ha
  exact ⟨bs, hs.1.preserveExternal hr hf hk (stable p a ha).1 (stable p a ha).2 hbs, hlen⟩

/-- The subgroup exponent's bytes are fixed by its public value and width. -/
theorem publicSubgroup_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a : Operand) (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer)
    (hin : ∀ p, (a, p.layout.pLen) ∈ inputs p)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a ⟨.input .q, .qLen⟩ (Core.element t) pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (PublicKeyPre inputs))
      (Core.publicPow M.mm pWorkspace a ⟨.input .q, .qLen⟩ (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  let pub (p : SchedulePublic) : ReadyCallPublic .p t :=
    scheduleCallPublic .p t (fun p => p.layout.pLen) (fun p => p.layout.qLen)
      (by intro p; have := p.layout.widths; omega_using [this]) (fun _ => Nat.le_refl _)
      (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this])
      (by decide) (element_space (by decide)) p
  refine two_post (two_map (fun p => (pub p, Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup)) ?_
    (PublicPower.readyPublicPow_ct M .p t a ⟨.input .q, .qLen⟩ ha (by trivial) hpa (by change Field.q ≠ .mask; decide) (by decide) hT)) ?_
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    have he : Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup = qb := by
      rw [← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    rw [he]
    exact ⟨⟨hs.1, ab, qb, hab.active, hqb.active, hal, hql⟩, hqb.active, hql⟩
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    refine WP.mono (readyPublicPow_ok M hs.1 .p p.pGreater p.pOdd a ⟨.input .q, .qLen⟩ ha (by trivial)
      hab.active hqb.active (by rw [hal]; have := p.layout.widths; omega)
      (by rw [hal]; exact Nat.le_refl _) (by rw [hql]; exact p.layout.widths.1)
      (by rw [hql]; have := p.layout.widths; omega_using [this]) t (by decide) (element_space (by decide) p))
      fun s' h => ⟨h.schedule hs (by decide) (element_space (by decide) p) (stable p),
        qb, h.external (by decide) (element_space (by decide) p) hqb, hql, hqv⟩

theorem publicIsOne_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.isOne pWorkspace (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  have ct := scheduleIsOne_ct inputs stable .p (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by trivial) (by intro p; have := p.layout.widths; omega_using [this])
    (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post (two_map (fun p => p) (fun p s h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) (ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  have hb := hs.1.readLocal .p t (by decide) (element_space (by decide) p)
  have hl : (Spec.Rsa.bytesAt s.mem (off p.layout.base t) p.layout.pLen).length = p.layout.pLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine WP.mono (readyIsOne_ok hs.1 .p (Core.element t) (by change t < 2 ^ 16; decide) hb
    (by simp only [ModulusSide.length]; rw [hl]; have := p.layout.widths; omega_using [this]) (by simp only [ModulusSide.length]; rw [hl]; exact Nat.le_refl _) hm)
    fun s' h => ⟨h.schedule hs (stable p), qb,
      h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of DSA domain and public-key validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem publicKey_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.publicKey M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hyct := publicSubgroup_ct M inputs stable Core.publicValue (by trivial) (by simp [stablePointer, Core.publicValue]) hy (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.publicKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct (RelCT.seq hone (RelCT.seq hyct hone)))).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p, hs.1, ht.1, hsp⟩)

theorem signingKey_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.signingKey M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.signingKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct hone)).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p, hs.1, ht.1, hsp⟩)

end VG.Proof.Dsa.AArch64
