module

import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateFn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_validate_private_key` on RISC-V: verified against the shared contract

`vpk_implies`: `vpkContract` implies the shared contract, with no stack of
its own; with correctness (`validatePriv_correct`) and constant time
(`validatePriv_ct`), `PrevalidatedSign.validate` is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- A state meeting `vpkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validatePrivSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 424 | .a2 => 128 | .a3 => 20 | .a4 => 0x10000 | .a5 => 2048 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 424⟩]
  wr := [⟨0x10000, 16384⟩]

theorem vpk_implies : vpkContract.Implies (Spec.Dsa.validatePrivateKeyContract RISCV64.abi) := by
  sig_implies [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, RISCV64.abi, RISCV64.argRegs,
    vpkContract, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validatePrivSatState] using validatePrivSatState

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivate_verified :
    Verified RISCV64.target PrevalidatedSign.validate (Spec.Dsa.validatePrivateKeyContract RISCV64.abi) :=
  Verified.of_correct validatePriv_correct CT.validatePriv_ct vpk_implies

end VG.Proof.Dsa.RISCV64
