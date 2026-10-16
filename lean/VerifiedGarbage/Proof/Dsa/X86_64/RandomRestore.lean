module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Framework.Omega

/-! Resume sampling after a signer call that preserves its inputs and private state. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomReadySlots : List Nat := [112, 120, 144, 176, 88, 184, 168, 160]

/-- Each sampling invocation tracks its own exact memory effects. The outer
signing loop separately tracks output and arithmetic-scratch writes. -/
theorem RandomReady.restore {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.gpr .rsp = s.gpr .rsp)
    (hwords : ∀ d ∈ randomReadySlots, word t.mem C.B d = word s.mem C.B d)
    (hrand : ∀ i < C.rand.length, t.mem (C.R + BitVec.ofNat 64 i) = s.mem (C.R + BitVec.ofNat 64 i))
    (hq : ∀ i < C.qBytes.length, t.mem (C.Q + BitVec.ofNat 64 i) = s.mem (C.Q + BitVec.ofNat 64 i))
    (hpad : ∀ i < C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1,
      t.mem (off C.B (200 + i)) = s.mem (off C.B (200 + i))) :
    RandomReady { C with initialMem := t.mem } used draws t := by
  refine ⟨h.scr.congr hwr, hsp.trans h.sp,
    (hwords _ (by decide)).trans h.rand,
    (hwords _ (by decide)).trans h.randLen,
    (hwords _ (by decide)).trans h.usedWord,
    (hwords _ (by decide)).trans h.width,
    (hwords _ (by decide)).trans h.qLen,
    (hwords _ (by decide)).trans h.mask,
    (hwords _ (by decide)).trans h.q,
    (hwords _ (by decide)).trans h.draws,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.randSrc.rd i hi,
      fun i hi => (hrand i hi).trans (h.randSrc.val i hi), h.randSrc.out⟩,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.qSrc.rd i hi,
      fun i hi => (hq i hi).trans (h.qSrc.val i hi), h.qSrc.out⟩,
    h.usedBound, Frm.refl _ _ _, fun i hi => (hpad i hi).trans (h.padding i hi)⟩

end VG.Proof.Dsa.X86_64
