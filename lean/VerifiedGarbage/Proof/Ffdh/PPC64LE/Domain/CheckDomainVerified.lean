module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_check_domain` on PPC64LE: verified against the shared contract

`cdContract` states the shared contract on the registers (`cd_implies`);
with correctness (`cd_correct`) and constant time (`cd_ct`), `checkDomain`
is verified (`cd_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- A state meeting `cdContract.pre`: a 512-bit p without q, the domain at
`0x1000` and the working space at `0x4000`. -/
def cdSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | .r5 => 64 | .r6 => 0x4000 | .r7 => 1056 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cd_implies : cdContract.Implies (Spec.Ffdh.checkDomainContract abi) := by
  sig_implies [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, cdContract,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [cdSatState] using cdSatState

end VG.Proof.Ffdh.PPC64LE.Domain
