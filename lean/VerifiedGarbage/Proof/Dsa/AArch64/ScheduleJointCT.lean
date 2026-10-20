module

public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint

/-! # Composable timing steps for complete DSA arithmetic schedules -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem scheduleJoint_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (d : Nat) (a b : Operand) (an bn : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (ha1 : ∀ p, 1 ≤ an p) (haw : ∀ p, (an p + 7) / 8 ≤ ModulusSide.p.words p.layout)
    (hb1 : ∀ p, 1 ≤ bn p) (hbw : ∀ p, (bn p + 7) / 8 ≤ ModulusSide.p.words p.layout)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 16) (hend : ∀ p : SchedulePublic, d + ModulusSide.p.length p.layout ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, ModulusSide.p.lengthField⟩ ModulusSide.p.offset)) hc).isSome = true) :
    RelCT isa (Two (ScheduleBinaryPre inputs a b an bn))
      (Core.joint M.mm ModulusSide.p.offset a b ⟨.local d, ModulusSide.p.lengthField⟩)
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .p d s) := by
  have hb1024 (p : SchedulePublic) : bn p ≤ 1024 := by
    have := hbw p
    have := (ModulusSide.p.bounds p.layout).2.1
    change ModulusSide.p.words p.layout ≤ 48 at this
    omega
  let pub (p : SchedulePublic) : ReadyProductPublic .p d :=
    { scheduleCallPublic .p d an bn ha1 haw hb1 hb1024 hd hend p with secondFits := hbw p }
  refine two_post (two_map pub ?_ (readyJoint_ct M d a b ha hb hpa hpb hd31 hT)) ?_
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    exact ⟨hs.1, ba, bb, has, hbs, hbl, hel⟩
  · intro p s ⟨hs, ⟨ba, has, hbl⟩, ⟨bb, hbs, hel⟩⟩
    obtain ⟨eb, he, hL⟩ := hs.1.availableLocal .q u (by decide) (scalar_space (by decide) p)
    obtain ⟨fb, hf, hF⟩ := hs.1.availableLocal .q v (by decide) (scalar_space (by decide) p)
    refine WP.mono (readyJoint_ok M hs.1 (p.greater .p) (p.odd .p) a b ha hb has hbs
      (hbl ▸ ha1 p) (hbl ▸ haw p) (hel ▸ hb1 p) (hel ▸ hbw p) he hf hL hF d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have : 1 < p.layout.modulus := p.greater .p; omega)) (p.fits .p)

end VG.Proof.Dsa.AArch64
