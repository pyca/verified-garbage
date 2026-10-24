module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_check_public` on PPC64LE: verified against the shared contract

`cpContract` states the shared contract on the registers (`cp_implies`);
with correctness (`cp_correct`) and constant time (`cp_ct`), `checkPublic`
is verified (`cp_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- A state meeting `cpContract.pre`: a 512-bit p without q, the domain at
`0x1000`, y at `0x2000` and the working space at `0x4000`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | .r5 => 64 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x4000 | .r9 => 1056
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cp_implies : cpContract.Implies (Spec.Ffdh.checkPublicContract abi) := by
  sig_implies [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, cpContract,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [satState] using satState

end VG.Proof.Ffdh.PPC64LE.Domain
