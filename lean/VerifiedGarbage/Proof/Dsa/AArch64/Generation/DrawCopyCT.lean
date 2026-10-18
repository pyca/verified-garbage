module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! Witness draws reveal their public tape position and widths. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate

structure DrawPublic where
  prime : PrimeParams
  used : Nat

def DrawBefore (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  PrimeState p.prime p.used s ∧ p.prime.len = len ∧ p.prime.drawBytes = drawBytes

def DrawCopyReady (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  s.gpr .x12 = off p.prime.rp (p.used + (drawBytes - len)) ∧ s.gpr .x2 = p.prime.p ∧
    s.gpr .x9 = BitVec.ofNat 64 len

theorem drawCopy_ct (len drawBytes : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc).isSome = true) :
    RelCT isa (Two (DrawBefore len drawBytes))
      (Impl.Dsa.AArch64.Generation.drawCopy len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.drawCopy
  refine RelCT.seq (two_post (Ψ := DrawCopyReady len drawBytes) (two_taint [.x0] ?_ ht) ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.ready.ws.x0.trans ht.1.ready.ws.x0.symm
  · intro p s h
    have hlen : len ≤ drawBytes := by rw [← h.2.1, ← h.2.2]; exact p.prime.lenDraw
    have hd : drawBytes < 4096 := by rw [← h.2.2]; have := p.prime.drawMax; omega
    exact WP.mono (drawCopyArgs_ok h.1.ready.ws hlen hd h.1.rand h.1.used h.1.ptr)
      fun t ⟨_, h12, h2, h9, _, _⟩ => ⟨h12, h2, h9⟩
  · exact two_taint [.x12, .x2, .x9] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
