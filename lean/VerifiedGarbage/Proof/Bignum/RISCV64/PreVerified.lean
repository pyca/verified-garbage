module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_public_precompute` on RISC-V -/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pre

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64.Precompute

/-- A state meeting `fnContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x4000 | .a5 => 112 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 896⟩]

theorem precompute_implies : fnContract.Implies (Spec.Rsa.publicPrecomputeContract RISCV64.abi) := by
  sig_implies [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, RISCV64.abi,
    RISCV64.argRegs, fnContract, preOut] [satState] using satState

/-- `vg_rsa_public_precompute`. -/
theorem precompute_verified :
    Verified RISCV64.target precompute (Spec.Rsa.publicPrecomputeContract RISCV64.abi) :=
  Verified.of_correct fn_correct fn_ct precompute_implies

end VG.Proof.Bignum.RISCV64.Pre
