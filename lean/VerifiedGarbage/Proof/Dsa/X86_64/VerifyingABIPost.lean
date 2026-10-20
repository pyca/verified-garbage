module
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReturn

import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingMain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Verification correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingGprPreserved {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, hsaved, hf, hk⟩ := hp
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
  · exact hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide))))

theorem verifyStatus_u32 (result : Bool) :
    ((BitVec.ofNat 64 result.toNat).setWidth 32).toNat = if result then 1 else 0 := by
  cases result <;> rfl

theorem verifyingSharedPost {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    (Spec.Dsa.verifyContract abi).post s t := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
  rw [hp.1, verifyStatus_u32]
  rfl

theorem verifyingCorrect (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.verify Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.verifyContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.verify Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyContract abi).post s t := by
  have ha := verifyingABI_of h
  obtain ⟨trace, t, he, hp⟩ := verifyingMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (verifyingGprPreserved ha hp), verifyingSharedPost ha hp⟩

end VG.Proof.Dsa.X86_64
