module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyImplies
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_verify_prevalidated` on PPC64LE: the contract on the registers and the stack

`prevalidated_implies`: `vpContract` implies the shared contract. The
witness is `vg_dsa_verify`'s (`satState`) with a key that passes validation
(`validKeyWitness`) at `0x1000`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `satState` with `validKeyWitness` at `0x1000`. -/
def prevalidatedSatState : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x1194 then
    VG.Proof.Dsa.validKeyWitness[a.toNat - 0x1000]?.getD 0 else satState.mem a
  rd := satState.rd
  wr := satState.wr

/-- The octets of a memory that holds `l` from `base` on. -/
theorem bytesAt_window {m : Mem} {base n : Nat} {l : List Byte} (hl : l.length = n) (hb : base + n < 2 ^ 64)
    (hm : ∀ a : Addr, base ≤ a.toNat → a.toNat < base + n → m a = l[a.toNat - base]?.getD 0) :
    Spec.Rsa.bytesAt m (BitVec.ofNat 64 base) n = l := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hl]
  · intro i h₁ h₂
    have hi : i < n := by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁; exact h₁
    have e : (BitVec.ofNat 64 base + BitVec.ofNat 64 i).toNat = base + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [hm _ (by omega) (by omega), e, Nat.add_sub_cancel_left, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem prevalidatedSat_key :
    Spec.Rsa.bytesAt prevalidatedSatState.mem 0x1000 404 = VG.Proof.Dsa.validKeyWitness :=
  bytesAt_window (base := 0x1000) VG.Proof.Dsa.validKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [prevalidatedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem prevalidated_implies : vpContract.Implies (Spec.Dsa.verifyPrevalidatedContract abi) where
  pre := by
    sig_implies_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
  post := by
    sig_implies_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
  pub := by
    sig_implies_pub [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
  sat := by
    have hv : Spec.Dsa.validatePublicKeyBytes 128 20
        (Spec.Rsa.bytesAt prevalidatedSatState.mem 0x1000 404) = true := by
      rw [prevalidatedSat_key]; exact VG.Proof.Dsa.validKeyWitness_valid
    refine ⟨prevalidatedSatState, ?_⟩
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_two,
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
         sig_simp_only [Region.Contains, prevalidatedSatState, satState, stackArg, stackArgAddr, Mem.readW,
           Mem.read] at h₁ h₂
         bv_omega)

end VG.Proof.Dsa.PPC64LE
