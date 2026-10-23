module

import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_public_precompute` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract on the registers
(`precompute_implies`); with correctness (`fn_correct`) and constant time
(`fn_ct`), `precompute` is verified (`precompute_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

/-- A state meeting `fnContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x4000 | .r8 => 112 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 896⟩]

theorem precompute_implies : fnContract.Implies (Spec.Rsa.publicPrecomputeContract abi) := by
  sig_implies [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, fnContract,
    preOut] [satState] using satState

/-- `vg_rsa_public_precompute`. -/
theorem precompute_verified : Verified target precompute (Spec.Rsa.publicPrecomputeContract abi) :=
  Verified.of_correct fn_correct fn_ct precompute_implies

end VG.Proof.Bignum.PPC64LE.Pre
