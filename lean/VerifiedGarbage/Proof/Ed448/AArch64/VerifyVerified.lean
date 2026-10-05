import VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain
import VerifiedGarbage.Proof.Ed448.AArch64.Erase
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on AArch64: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
files pass in); constant time (by taint tracking: the only branches are on
the loop counters, and every address is an argument plus a constant or a
counter); and a concrete state satisfying the signature's contract. The
contract lets timing depend on the inputs; the code's depends on the pointers
alone.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

def verifyEquationSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (s : State)
    (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct hR hE hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, Exec.preservedV he
    (Code.allInstrs_keepsV_of_eraseOff_eq verifyEquation_eraseOff (by lit_decide))⟩, h.2⟩

theorem verifyEquation_noFrames : verifyEquation.noFrames = true := by
  rw [← Code.noFrames_eraseOff, verifyEquation_eraseOff, Code.noFrames_eraseOff]; decide +kernel

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    -- The hint keeps public only the pointers and the counter, which the addresses and
    -- branches use: every field operation is then analysed from the same taint.
    (Taint.isSome_check_of_eraseOff verifyEquation_eraseOff
      (by taint_decide_weak fun τ => τ.inter (Taint.ofRegs [.x0, .x1, .x2, .x3, .x19, .x20])))
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, verifyEquationLocal]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs]
    have h' : t.gpr .x0 = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, -, pk, sig, ch, base⟩ := h
    exact ⟨sp, pk, sig, ch, base⟩
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs] [verifyEquationSat] using verifyEquationSat

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    Verified AArch64.target verifyEquation (Spec.Ed448.verifyEquationContract AArch64.abi) :=
  Verified.of_correct (verifyEquation_ok hR hE) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.AArch64
