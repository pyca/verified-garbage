module

public import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Verify
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Verify
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P192
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA verification over P-192 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public, although the contract lets every input
affect timing).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.P192

theorem verify_ct : ConstantTime isa verifyRV.pre verifyRV.pub verifyP192 :=
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
  rd := [⟨0x1000, 49⟩, ⟨0x2000, 24⟩, ⟨0x3000, 48⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifyP192 (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.P192.inst RISCV64.abi) :=
  Verified.of_correct (verify_rv hL) verify_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }


/-- `verifySat` satisfies the precondition. -/
theorem verify_sat : (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.P192.inst RISCV64.abi).pre verifySat := by
  sig_pre [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P192.curve, Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, verifySat]
  repeat' (first | exact Region.disjoint_of_sep (by decide) | decide | rfl | constructor)

/-- `vg_ecdsa_p192_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_nil`). -/
theorem verifyHash_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target
      (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false Impl.Ecdsa.RISCV64.P192.verifyP192)
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.P192.inst RISCV64.abi 80) :=
  Proof.Ecdsa.Verify.RISCV64.verifyHash_verified_nil Proof.Ecdsa.Verify.p192_len (by decide) (verify_verified hL)
    (by taint_decide) (Proof.Ecdsa.Verify.RISCV64.hashSat_nil (by decide) verify_sat (by decide) fun r hr => by
      simp only [verifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.RISCV64.P192
