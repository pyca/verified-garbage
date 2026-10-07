import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_public_precompute` on AArch64: verified against the shared contract

`pcContract` states the shared contract on the registers
(`precompute_implies`); with correctness (`pcCode_correct`) and constant
time (`pcCode_constantTime`), `Precompute.code` is verified
(`precompute_verified`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64

/-- A state meeting `pcContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def pcSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x4000 | .x5 => 1024 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8192⟩]

theorem precompute_implies : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi) := by
  sig_implies [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract]
    [pcSatState] using pcSatState

/-- `vg_rsa_public_precompute` with Montgomery multiplication `M`. -/
theorem precompute_verified (M : Mont) :
    Verified target (Precompute.code M.mm) (Spec.Rsa.publicPrecomputeContract abi) :=
  Verified.of_correct (pcCode_correct M) (pcCode_constantTime M) precompute_implies

end VG.Proof.Bignum.AArch64
