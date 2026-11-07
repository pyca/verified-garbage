module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.DomainChecked
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCheckedCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveImplies
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedImplies
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
public import VerifiedGarbage.Proof.Dsa.Validation
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_derive_key_checked` on RISC-V: verified against the shared contract

`dcContract` implies `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`), with no stack of its own
(`deriveChecked_implies`); with correctness (`deriveChecked_correct`) and
constant time (`CT.deriveChecked_ct`), `Generate.deriveChecked` is verified
(`deriveChecked_verified`). Key generation calls it, on `dcContract`, once
its domain check has returned 1 (`GKDerive.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `deriveSatState` with `validKeyWitness` at `0x1000`: its first 276
octets, the domain. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  sp := deriveSatState.sp
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x1194 then
    VG.Proof.Dsa.validKeyWitness[a.toNat - 0x1000]?.getD 0 else deriveSatState.mem a
  rd := deriveSatState.rd
  wr := deriveSatState.wr

theorem deriveCheckedSat_key :
    Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x1000 404 = VG.Proof.Dsa.validKeyWitness :=
  bytesAt_window (base := 0x1000) VG.Proof.Dsa.validKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [deriveCheckedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

/-- The witness's domain passes the checks, as its key passes validation. -/
theorem deriveCheckedSat_params :
    Spec.Dsa.checkParametersBytes 128 20 (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x1000 276) = true := by
  have hv : Spec.Dsa.lengthsValid (⟨0, 0, 128, 20⟩ : Lay).pl (⟨0, 0, 128, 20⟩ : Lay).ql := by decide
  have hk : Spec.Dsa.validatePublicKeyBytes 128 20 (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x1000 404) = true := by
    rw [deriveCheckedSat_key]; exact VG.Proof.Dsa.validKeyWitness_valid
  have hK : KeyOk deriveCheckedSatState.mem ⟨0, 0, 128, 20⟩ 0x1000 :=
    of_decide_eq_true ((validate_spec (m := deriveCheckedSatState.mem) (key := 0x1000) hv).symm.trans hk)
  exact (checkParameters_spec (m := deriveCheckedSatState.mem) (key := 0x1000) hv).trans
    (decide_eq_true (keyOk_iff.mp hK).1)

theorem deriveChecked_implies : dcContract.Implies (Spec.Dsa.deriveKeyDomainCheckedContract RISCV64.abi) where
  pre := by
    sig_implies_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, RISCV64.abi, RISCV64.argRegs,
      dcContract, dContract, dRes, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero,
      Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true,
      Bool.or_false, List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  post := by
    sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, RISCV64.abi, RISCV64.argRegs,
      dcContract, dContract, dRes, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero,
      Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true,
      Bool.or_false, List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  pub := by
    sig_implies_pub [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, RISCV64.abi, RISCV64.argRegs,
      dcContract, dContract, dRes, stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero,
      Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true,
      Bool.or_false, List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two,
      List.range, List.range.loop]
  sat := by
    refine ⟨deriveCheckedSatState, ?_⟩
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, RISCV64.abi, RISCV64.argRegs,
      stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
      List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
      List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
    sig_and_intros
    all_goals first
      | (rw [show BitVec.toNat (128 : BitVec 64) = 128 from rfl, show BitVec.toNat (20 : BitVec 64) = 20 from rfl,
          show BitVec.toNat (276 : BitVec 64) = 276 from rfl]
         exact deriveCheckedSat_params)
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro a h₁ h₂
         sig_simp_only [Region.Contains, deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW,
           Mem.read] at h₁ h₂
         bv_omega)

/-- `vg_dsa_derive_key_checked`. -/
theorem deriveChecked_verified :
    Verified RISCV64.target Generate.deriveChecked (Spec.Dsa.deriveKeyDomainCheckedContract RISCV64.abi) :=
  Verified.of_correct deriveChecked_correct CT.deriveChecked_ct deriveChecked_implies

end VG.Proof.Dsa.RISCV64
