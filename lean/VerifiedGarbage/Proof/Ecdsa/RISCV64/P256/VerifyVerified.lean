module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Verify
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Verify
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P256
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA verification over P-256 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public, although the contract lets every input
affect timing).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify

theorem verify_ct : ConstantTime isa verifyRV.pre verifyRV.pub verifyP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifyP256 (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.P256.inst RISCV64.abi) :=
  Verified.of_correct (verify_rv hL) verify_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }

end VG.Proof.Ecdsa.RISCV64.P256
