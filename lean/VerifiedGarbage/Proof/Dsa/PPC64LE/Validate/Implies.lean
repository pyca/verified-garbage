module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_validate_public_key` on PPC64LE: the contract on the registers

`validate_implies`: `vkContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- A state meeting `vkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validateSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 404 | .r5 => 128 | .r6 => 20 | .r7 => 0x10000 | .r8 => 2048 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 404⟩]
  wr := [⟨0x10000, 16384⟩]

theorem validate_implies : vkContract.Implies (Spec.Dsa.validatePublicKeyContract abi) := by
  sig_implies [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, vkContract,
    List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validateSatState] using validateSatState

end VG.Proof.Dsa.PPC64LE
