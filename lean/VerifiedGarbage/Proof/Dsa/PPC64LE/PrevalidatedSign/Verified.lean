module

import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.ValidateCT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Validate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_validate_private_key` on PPC64LE: verified against the shared contract

`vpkContract` states the shared contract on the registers
(`validatePrivate_implies`); with correctness (`validatePrivate_correct`) and
constant time (`validatePrivate_ct`), `PrevalidatedSign.validate` is verified
(`validatePrivate_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- A state meeting `vpkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validatePrivateSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 424 | .r5 => 128 | .r6 => 20 | .r7 => 0x10000 | .r8 => 2048 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 424⟩]
  wr := [⟨0x10000, 16384⟩]

theorem validatePrivate_implies : vpkContract.Implies (Spec.Dsa.validatePrivateKeyContract abi) := by
  sig_implies [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, vpkContract,
    vpkRes, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validatePrivateSatState] using validatePrivateSatState

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivate_verified :
    Verified target PrevalidatedSign.validate (Spec.Dsa.validatePrivateKeyContract abi) :=
  Verified.of_correct validatePrivate_correct validatePrivate_ct validatePrivate_implies

end VG.Proof.Dsa.PPC64LE
