module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState

/-! # Constant time of p reduction from X and 2q -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64

theorem reductionCopy_ct : RelCT isa (Two ReductionStart) (copyA 4 0) (Two ReductionCopied) := by
  have e : copyA 4 0 = .seq (.block (ws ++ (base 0 .rsi ++ base 4 .rbx)))
      VG.Impl.Rsa.X86_64.copyWords := by simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => by rw [← e]; exact reductionCopy_state h)

theorem reductionDivide_ct :
    RelCT isa (Two ReductionCopied) (divmod 0 1 2 3) (Two ReductionDivided) :=
  candidateDivmod_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1.1) (fun _ _ h => reductionDivide_state h)

theorem reductionSubtract_ct : RelCT isa (Two ReductionDivided)
    (Impl.Dsa.X86_64.Generation.subtractRemainder 5 4 1) (Two ReductionSubtracted) :=
  subtractRemainder_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1) 5 4 1 (by taint_decide) (fun _ _ h => reductionSubtract_state h)

theorem reductionIncrement_ct : RelCT isa (Two ReductionSubtracted)
    (.block (Impl.Dsa.X86_64.Generation.incrementEven 5)) (fun _ _ => True) := by
  have ct := incrementEven_ct (Φ := ReductionSubtracted) (Ψ := fun _ _ => True)
    ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1) 5 (by taint_decide)
    (fun _ _ h => WP.mono (incrementEven_ok h.1 (by decide : 5 < 16) h.2) (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem reduceCandidate_ct : RelCT isa (Two ReductionStart)
    Impl.Dsa.X86_64.Generation.reduceCandidate (fun _ _ => True) :=
  RelCT.seq reductionCopy_ct (RelCT.seq reductionDivide_ct (RelCT.seq reductionSubtract_ct reductionIncrement_ct))

end VG.Proof.Dsa.X86_64.Generation
