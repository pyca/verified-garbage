module

public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.MinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyByteChecksCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT

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
