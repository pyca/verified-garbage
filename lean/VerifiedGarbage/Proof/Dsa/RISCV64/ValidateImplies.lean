module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_validate_public_key` on RISC-V: the shared contract

`validate_implies`: `vkContract` implies the shared contract; `validate_wp`:
`vg_dsa_validate_public_key` meets it, with no stack of its own.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- A state meeting `vkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validateSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 404 | .a2 => 128 | .a3 => 20 | .a4 => 0x10000 | .a5 => 2048 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 404⟩]
  wr := [⟨0x10000, 16384⟩]

theorem validate_implies : vkContract.Implies (Spec.Dsa.validatePublicKeyContract RISCV64.abi) := by
  sig_implies [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, RISCV64.abi, RISCV64.argRegs,
    vkContract, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validateSatState] using validateSatState

/-- `vg_dsa_validate_public_key` under the shared contract. -/
theorem validate_wp (s : State) (h : (Spec.Dsa.validatePublicKeyContract RISCV64.abi).pre s) :
    WP isa Prevalidated.validate s fun t =>
      abiPreserved s t ∧ (Spec.Dsa.validatePublicKeyContract RISCV64.abi).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := validate_correct s (validate_implies.pre s h)
  exact ⟨tr, t, he, ha, validate_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
