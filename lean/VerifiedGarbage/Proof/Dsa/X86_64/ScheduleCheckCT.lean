module

public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
public import VerifiedGarbage.Proof.Dsa.X86_64.MinusCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.X86_64.ReadyMinusCT`, which this module and modules that import it used -/

section

/-! # Constant-time construction of p-minus-one and q-minus-two -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    {s : State} (hd31 : d < 2 ^ 31) (hr : Ready p.layout s) :
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
    rw [hk.2.2]
    exact hr.local_write p.outputEnd j hj

theorem readyMinus_ct (side : ModulusSide) (amount d : Nat)
    (ha : amount < 2 ^ 31) (hd31 : d < 2 ^ 31)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) h₂).isSome = true) :
    RelCT isa (Two fun p : ReadyMinusPublic side amount d => Ready p.layout)
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block ((Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++
    Core.enter side.offset) ++ minusHead amount)) (.seq (wordLoop 1 minusTail) (seqs Core.finish))) _
  apply fuseBlocks_ct
  refine RelCT.seq (two_piece (Ψ := fun p s => MinusPre p.call s) [.rdi]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.parent.rdi)) ht₁ (fun _ _ h => minusCallHead_ok hd31 h)) ?_
  exact RelCT.assoc (two_map ReadyMinusPublic.call (fun _ _ h => h) (minusFinish_ct amount ha ht₂))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReadyRangeCT`, which this module and modules that import it used -/

section

/-! # Range-check timing in the complete DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCheckPre side a)) (Checks.range side.offset a aboveOne) (fun _ _ => True) := by
  unfold Checks.range seqs
  refine RelCT.seq (two_piece (Ψ := fun p s => LPre aX arg argLen (p.bytes a) s) [.rdi]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.parent.rdi)) hT (fun _ _ h => checkHead_ok ha hp h)) ?_
  refine RelCT.seq (two_map (fun p : ReadyCheckPublic side => p.bytes a) (fun _ _ h => h) loadCheck_ct) ?_
  refine RelCT.seq (loadedRange_ct aboveOne) ?_
  exact two_map (fun p : BPub => p.x) (fun _ _ h => h) leaveAccumulate_ct

theorem readyIsOne_ct (side : ModulusSide) (a : Operand)
    (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand arg argLen a ++ Core.enter side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCheckPre side a)) (Checks.isOne side.offset a) (fun _ _ => True) := by
  unfold Checks.isOne seqs
  refine RelCT.seq (two_piece (Ψ := fun p s => LPre aX arg argLen (p.bytes a) s) [.rdi]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.parent.rdi)) hT (fun _ _ h => checkHead_ok ha hp h)) ?_
  exact RelCT.seq (two_map (fun p : ReadyCheckPublic side => p.bytes a) (fun _ _ h => h) loadCheck_ct)
    oneReturn_ct

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReadyByteChecksCT`, which only this module used -/

section

/-! # Byte validation timing from the persistent public field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem readyZero_ct {a : Operand} (ha : pointerFits a.pointer)
    (hp : stablePointer a.pointer) (hl : a.length ≠ .mask) (nonzero : Bool)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.zero a nonzero) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, (L.fields a.length).toNat⟩ : ZeroPublic)) ?_ (zero_ct ha nonzero hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.rdi, h.publicPointer a.pointer hp, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

theorem readyEqual_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hl : a.length ≠ .mask) (unequal : Bool)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax)] : List Instr) ++ Core.pointer b.pointer ++
      ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.equal a b unequal) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, L.pointer b.pointer, (L.fields a.length).toNat⟩ : EqualPublic)) ?_
    (equal_ct ha hb unequal hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.rdi,
    h.publicPointer a.pointer hpa, h.publicPointer b.pointer hpb, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

end VG.Proof.Dsa.X86_64

end

end


/-! # Validation timing steps that preserve the complete schedule state -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax)] : List Instr) ++ Core.pointer b.pointer ++
      ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
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
    (side : ModulusSide) (amount d : Nat) (ha : amount < 2 ^ 31)
    (ham : ∀ p : SchedulePublic, amount ≤ side.value p.layout)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 31)
    (hend : ∀ p : SchedulePublic, d + side.length p.layout ≤ usedBytes)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) h₂).isSome = true) :
    RelCT isa (Two (ScheduleState inputs))
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (Two (ScheduleState inputs)) := by
  refine two_post (two_map (fun p : SchedulePublic =>
    (⟨p.layout, ham p, hd, hend p⟩ : ReadyMinusPublic side amount d))
    (fun _ _ h => h.1) (readyMinus_ct side amount d ha hd31 ht₁ ht₂)) ?_
  intro p s hs
  exact WP.mono (readyMinus_ok hs.1 side amount ha (ham p) d hd (hend p))
    fun t h => h.schedule hs hd (hend p) (stable p)

end VG.Proof.Dsa.X86_64
