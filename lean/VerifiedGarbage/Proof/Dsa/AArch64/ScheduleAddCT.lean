module
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands

/-! # Timing of adding the two reduced signing scalars -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem scheduleScalarAdd_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a b d : Nat) (ha : activeBytes ≤ a) (hb : activeBytes ≤ b) (hd : activeBytes ≤ d)
    (ha31 : a < 2 ^ 16) (hb31 : b < 2 ^ 16) (hd31 : d < 2 ^ 16)
    (hae : ∀ p : SchedulePublic, a + p.layout.qLen ≤ usedBytes)
    (hbe : ∀ p : SchedulePublic, b + p.layout.qLen ≤ usedBytes)
    (hde : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead (Core.scalar a) (Core.scalar b) (Core.scalar d) qWorkspace)) hc).isSome = true) :
    RelCT isa (Two fun p s => ScheduleState inputs p s ∧
      LocalReduced p.layout .q a s ∧ LocalReduced p.layout .q b s)
      (Core.add (Core.scalar a) (Core.scalar b) (Core.scalar d))
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .q d s) := by
  let pub (p : SchedulePublic) : ReadyProductPublic .q d :=
    { layout := p.layout, baseLen := p.layout.qLen, exponentLen := p.layout.qLen,
      greater := p.greater .q, odd := p.qOdd, basePositive := p.layout.widths.1,
      baseFits := Nat.le_refl _, exponentPositive := p.layout.widths.1,
      exponentBound := Nat.le_trans p.layout.widths.2.1 (by decide),
      outputStart := hd, outputEnd := hde p, secondFits := Nat.le_refl _ }
  refine two_post (two_map pub ?_
    (readyAdd_ct d (Core.scalar a) (Core.scalar b) ha31 hb31 trivial trivial hd31 hT)) ?_
  · intro p s ⟨hs, hra, hrb⟩
    obtain ⟨ba, has, hal⟩ := hs.1.availableLocal .q a ha (hae p)
    obtain ⟨bb, hbs, hbl⟩ := hs.1.availableLocal .q b hb (hbe p)
    exact ⟨⟨hs.1, ba, bb, has, hbs, hal, hbl⟩, hra, hrb⟩
  · intro p s ⟨hs, hra, hrb⟩
    have has := hs.1.readLocal .q a ha (hae p)
    have hbs := hs.1.readLocal .q b hb (hbe p)
    have lena : (Spec.Rsa.bytesAt s.mem (off p.layout.base a) p.layout.qLen).length = p.layout.qLen := by
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have lenb : (Spec.Rsa.bytesAt s.mem (off p.layout.base b) p.layout.qLen).length = p.layout.qLen := by
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    refine WP.mono (readyAdd_ok hs.1 (Core.scalar a) (Core.scalar b) ha31 hb31 has hbs
      (by change 1 ≤ (Spec.Rsa.bytesAt s.mem (off p.layout.base a) p.layout.qLen).length; rw [lena]; exact p.layout.widths.1)
      (by simp only [ModulusSide.length, lena]; exact Nat.le_refl _)
      (by change 1 ≤ (Spec.Rsa.bytesAt s.mem (off p.layout.base b) p.layout.qLen).length; rw [lenb]; exact p.layout.widths.1)
      (by simp only [ModulusSide.length, lenb]; exact Nat.le_refl _) hra hrb d hd (hde p))
      fun t h => ⟨h.schedule hs hd (hde p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega)) p.qFits

end VG.Proof.Dsa.AArch64
