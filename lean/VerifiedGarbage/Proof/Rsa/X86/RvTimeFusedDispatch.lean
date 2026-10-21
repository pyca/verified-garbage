module

import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedRest
import VerifiedGarbage.Proof.Rsa.X86.RvFusedDispatch
import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
meta import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
public import VerifiedGarbage.Proof.Rsa.X86.RvTimePrepare
meta import VerifiedGarbage.Proof.Rsa.X86.RvTimePrepare
import VerifiedGarbage.Proof.Rsa.X86.RvTimeRest
meta import VerifiedGarbage.Proof.Rsa.X86.RvTimeRest

/-! The modulus-length dispatch leaks only a public argument. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Rsa (recoverPrimes)

theorem recoveryChoiceCheck : (VG.Taint.check taint τA (.block VG.Impl.Rsa.X86.RecoverRt.recoveryChoice)
    (VG.Taint.hintOf taint τA (.block VG.Impl.Rsa.X86.RecoverRt.recoveryChoice))).isSome=true := by
  taint_decide

theorem selectedRest_relCT (g : CallGeometry) (pg : PubG g.toGeo) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0)
    (goS : GoOn (product g s0.mem)) (goT : GoOn (product g t0.mem))
    (boundS : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (boundT : inputValue g t0.mem 0 < 2 ^ (64 * g.n))
    (oddS : inputValue g s0.mem 0 % 2 = 1) (oddT : inputValue g t0.mem 0 % 2 = 1)
    (largeS : 101 < inputValue g s0.mem 0) (largeT : 101 < inputValue g t0.mem 0)
    (modulus : inputValue g s0.mem 0 = inputValue g t0.mem 0)
    (tries : (recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2 =
      (recoverPrimes (inputValue g t0.mem 0) (inputValue g t0.mem 1) (inputValue g t0.mem 2)).2) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) VG.Impl.Rsa.X86.RecoverRt.selectedRest
      (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.selectedRest
  refine VG.RelCT.seq (R := fun (s t : State) =>
    (NumbersState g s0 s ∧ s.cf=some (decide ((g.args 5).toNat<256))) ∧
    (NumbersState g t0 t ∧ t.cf=some (decide ((g.args 5).toNat<256))))
    (pub_relCT (P := NumbersState g s0) (Q := NumbersState g t0)
      (P' := fun s => NumbersState g s0 s ∧ s.cf=some (decide ((g.args 5).toNat<256)))
      (Q' := fun t => NumbersState g t0 t ∧ t.cf=some (decide ((g.args 5).toNat<256)))
      pg recoveryChoiceCheck (fun _ h => KS.stage h) (fun _ h => KS.stage h)
      (fun _ h => recoveryChoice_ok h) (fun _ h => recoveryChoice_ok h)) ?_
  apply VG.RelCT.iteCold
  refine VG.RelCT.ite (fun s t ⟨⟨_,cs⟩,⟨_,ct⟩⟩ => by change s.cf=t.cf; rw [cs,ct]) ?_ ?_
  · exact (rest_relCT g pg s0 t0 left right goS goT boundS boundT oddS oddT largeS largeT modulus tries).mono
      (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ _ => trivial)
  · exact (fusedRest_relCT g pg s0 t0 left right goS goT boundS boundT oddS oddT largeS largeT modulus tries).mono
      (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86.Recover
