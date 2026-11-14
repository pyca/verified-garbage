module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningReturn
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.X86_64.SigningMain`, which only this module used -/

section

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

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingGprPreserved {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, _, hsaved, hf, hk⟩ := hp
  refine ⟨?_, Mem.readW_congr fun i hi => ?_⟩
  · intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · exact hk.gpr (by decide)
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · have hret := contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide)
    apply hf _ (Nat.le_trans h.used (out_scr h.retScratch hret))
    intro j hj he
    apply h.retOut _ hret
    rw [he]
    exact contains_byte _ (by change j < 2 * (stackArg s 0).toNat at hj; rw [h.outLength]; exact hj)
      (Nat.le_of_lt (s.gpr .rsi).isLt)

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (signingGprPreserved ha hp), signingSharedPost ha hp⟩

end VG.Proof.Dsa.X86_64
