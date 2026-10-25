module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReturn
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedReturn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingShape
public import VerifiedGarbage.Spec.Dsa.Prevalidated

/-! # Functional correctness of the complete AArch64 DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSuccess_ok (M : Mont) {p : VerifyingInput} {original st : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength st) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (seqs [SignVerify.workspaces, Prevalidated.compute M.mm, .block SignVerify.result]) st
      (VerifyingPost p original) := by
  refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
  exact prevalidatedAccepted_ok M h ht ha hv

theorem prevalidatedMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (Prevalidated.verify M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => prevalidatedSuccess_ok M h hs ha hv)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64
