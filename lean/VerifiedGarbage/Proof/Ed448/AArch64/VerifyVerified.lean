import VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Front
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Windows
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness including the ABI,
given decoding's agreement with the specification (`RecoverOk`, which the
registration files pass in); constant time (by taint tracking, phase by phase, `VerifyCT/`: the only
branches are on the counters, every address is an argument plus a constant
or a counter, and the digits' masks only select; checked on the code without
its immediates, `VerifyErase.lean`); and a concrete state satisfying the
signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone.
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

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct hR hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  obtain ⟨_, e₁⟩ := front_ct
  obtain ⟨_, e₂⟩ := table_ct
  obtain ⟨_, e₃⟩ := sBase_ct
  obtain ⟨_, e₄⟩ := kWindows_ct
  obtain ⟨_, e₅⟩ := tail_ct
  refine Taint.constantTime_eraseImm_of_eq (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ verifyEquation_eraseImm
    (seq_ok e₁ (seq_ok e₂ (seq_ok e₃ (seq_ok e₄ e₅))))
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem verifyEquation_eqOk (hR : Proof.Ed448.RecoverOk) : EqOk := ⟨verifyEquation_ok hR, verifyEquation_ct⟩

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

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) :
    Verified AArch64.target verifyEquation (Spec.Ed448.verifyEquationContract AArch64.abi) :=
  Verified.of_correct (verifyEquation_ok hR) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.AArch64
