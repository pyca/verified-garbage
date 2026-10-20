module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReturn
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Functional correctness of the complete x86-64 DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingSuccess_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original st : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.publicKey Sq.mm M.mm,
      Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
      Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR, .block SignVerify.result]) st
      (VerifyingPost p original) := by
  refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := verifyingAccepted_ok M Sq h ht ha
  apply wpAppendSequences (a := [Checks.publicKey Sq.mm M.mm,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR])
    (b := [.block SignVerify.result]) (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem verifyingMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0) :
    WP isa (SignVerify.verify Sq.mm M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => verifyingSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64
