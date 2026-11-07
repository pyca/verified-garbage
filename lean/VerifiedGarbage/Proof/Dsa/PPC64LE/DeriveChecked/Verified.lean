module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Implies
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Implies
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.DomainChecked
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# DSA key derivation for a checked domain on PPC64LE: verified against its contract

`deriveChecked_implies`: `dcContract` implies `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`), `deriveKeyContract` for a domain whose exact
octets pass `checkParametersBytes`. The witness is `vg_dsa_derive_key`'s
(`deriveSatState`) with a domain that passes the checks (`validDomainWitness`)
at `0x1000`. With correctness (`deriveChecked_correct`) and constant time
(`deriveChecked_ct`), `Derive.deriveChecked`, which key generation calls, is
verified (`deriveChecked_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `validKeyWitness`'s domain, the first 276 of its octets. -/
def validDomainWitness : List Byte := VG.Proof.Dsa.validKeyWitness.take 276

theorem validDomainWitness_length : validDomainWitness.length = 276 := by
  simp only [validDomainWitness, List.length_take, VG.Proof.Dsa.validKeyWitness_length]; rfl

theorem validDomainWitness_valid : Spec.Dsa.checkParametersBytes 128 20 validDomainWitness = true := by
  decide +kernel

/-- `deriveSatState` with `validDomainWitness` at `0x1000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  lr := deriveSatState.lr
  sp := deriveSatState.sp
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x1114 then
    validDomainWitness[a.toNat - 0x1000]?.getD 0 else deriveSatState.mem a
  rd := deriveSatState.rd
  wr := deriveSatState.wr

theorem deriveCheckedSat_domain :
    Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x1000 276 = validDomainWitness :=
  bytesAt_window (base := 0x1000) validDomainWitness_length (by decide) fun a h₁ h₂ => by
    simp only [deriveCheckedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem deriveChecked_implies : dcContract.Implies (Spec.Dsa.deriveKeyDomainCheckedContract abi) where
  pre := by
    sig_implies_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, dcContract,
      dContract, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  post := by
    sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, dcContract,
      dContract, dRes, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  pub := by
    sig_implies_pub [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, dcContract,
      dContract, dRes, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  sat := by
    have hv : Spec.Dsa.checkParametersBytes 128 20
        (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x1000 276) = true := by
      rw [deriveCheckedSat_domain]; exact validDomainWitness_valid
    refine ⟨deriveCheckedSatState, ?_⟩
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_one,
      List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
      List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
      List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
    sig_and_intros
    rotate_right
    · exact hv
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro a h₁ h₂
         sig_simp_only [Region.Contains, deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr,
           Mem.readW, Mem.read] at h₁ h₂
         bv_omega)

/-- `vg_dsa_derive_key_checked`, against `deriveKeyDomainCheckedContract`. -/
theorem deriveChecked_verified :
    Verified target Derive.deriveChecked (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  Verified.of_correct deriveChecked_correct deriveChecked_ct deriveChecked_implies

end VG.Proof.Dsa.PPC64LE
