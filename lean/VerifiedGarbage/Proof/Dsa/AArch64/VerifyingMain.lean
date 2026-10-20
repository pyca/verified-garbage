module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReturn
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block

/-! # Functional correctness of the complete AArch64 DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyingSuccess_ok (M : Mont) {p : VerifyingInput} {original st : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.publicKey M.mm,
      Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
      Core.verify M.mm, Checks.equal (Core.scalar u) Core.signatureR, .block SignVerify.result]) st
      (VerifyingPost p original) := by
  refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := verifyingAccepted_ok M h ht ha
  apply wpAppendSequences (a := [Checks.publicKey M.mm,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify M.mm, Checks.equal (Core.scalar u) Core.signatureR])
    (b := [.block SignVerify.result]) (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem verifyingMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0) :
    WP isa (SignVerify.verify M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => verifyingSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64
