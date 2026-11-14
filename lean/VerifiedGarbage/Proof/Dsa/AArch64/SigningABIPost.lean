module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningReturn
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPre
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Dsa.AArch64.SigningMain`, which only this module used -/

section

/-! # Functional correctness of the complete AArch64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingSuccess_ok (M : Mont) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
      Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M h ht ha
  apply wpAppendSequences (a := [Checks.signingKey M.mm, Checks.privateKey M.mm,
    Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M ha.pre
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2.2, signingSharedPost ha hp⟩

end VG.Proof.Dsa.AArch64
