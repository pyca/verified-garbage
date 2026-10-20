module

public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.Arithmetic

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
    exact h.reduced (VG.Proof.Dsa.powMod_lt _ _ (by have := p.greater side; omega)) (p.fits side)

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
    omega
  let pub (p : SchedulePublic) : ReadyProductPublic side d :=
    { scheduleCallPublic side d an bn ha1 haw hb1 hb1024 hd hend p with secondFits := hbw p }
  refine two_post (two_map pub ?_ (readyProduct_ct M side d a b ha hb hpa hpb hd31 hT)) ?_
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    exact ⟨hs.1, ba, bb, has, hbs, hbl, hel⟩
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    refine WP.mono (readyProduct_ok M hs.1 side (p.greater side) (p.odd side) a b ha hb has hbs
      (hbl ▸ ha1 p) (hbl ▸ haw p) (hel ▸ hb1 p) (hel ▸ hbw p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have := p.greater side; omega)) (p.fits side)

end VG.Proof.Dsa.AArch64
