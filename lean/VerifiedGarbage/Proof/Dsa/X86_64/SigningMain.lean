module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningReturn
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Functional correctness of the complete x86-64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingSuccess_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
      Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M Sq h ht ha
  apply wpAppendSequences (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) (Sq : MontS) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign Sq.mm M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64
