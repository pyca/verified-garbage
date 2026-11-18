module

public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Minus
public import VerifiedGarbage.Proof.Dsa.AArch64.Product
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Product
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead

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
