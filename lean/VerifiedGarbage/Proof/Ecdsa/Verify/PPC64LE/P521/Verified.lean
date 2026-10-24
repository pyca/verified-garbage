module

import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Contract
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Contract
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P521
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

/-!
# ECDSA verification over P-521 on PPC64LE: `Verified`

`verify_ppc`: from `verify_ok`, for P-521's configuration; `verify_ct`: the
time depends only on the pointers (`taint_decide` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P521

open VG VG.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : verifyPPC.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem verify_ppc (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : verifyPPC.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := verify_ok p521_ok (by decide) hL (pre_of hs)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

theorem verify_ct : ConstantTime isa verifyPPC.pre verifyPPC.pub verifyP521 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5, h6⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 133⟩, ⟨0x2000, 66⟩, ⟨0x3000, 132⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified PPC64LE.target verifyP521 (Spec.Ecdsa.P521.inst.verifyContract PPC64LE.abi) :=
  Verified.of_correct (verify_ppc hL) verify_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
        simp only [verifyPPC, vf, Spec.P521.curve] at h
        revert h
        split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
          exact fun h => by rw [h]; rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }

end VG.Proof.Ecdsa.Verify.PPC64LE.P521
