module

import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Recognize

/-! Public anchors permit unrelated nonvolatile registers and scratch contents. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

structure Start (a s : State) : Prop where
  pre : contract.pre s
  stack : s.gpr .esp = a.gpr .esp
  args : ∀ i < 5, arg s i = arg a i
  domain : domain s = domain a
  symbol : s.syms tableSym = a.syms tableSym

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], symAddr s c.1 = symAddr t c.1) : s.syms name = t.syms name := by
  have wide := h (name, words) List.mem_cons_self
  have value := congrArg BitVec.toNat wide
  apply BitVec.eq_of_toNat_eq
  simpa only [symAddr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt
    (Nat.lt_trans (s.syms name).isLt (by decide : 2 ^ 32 < 2 ^ 64)), Nat.mod_eq_of_lt
    (Nat.lt_trans (t.syms name).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using value

theorem start_of_pub {a s : State} (h : contract.pre s) (pub : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi 172).pub a s ∧
      ∀ c ∈ tableConsts, symAddr a c.1 = symAddr s c.1 := pub_consts.mp pub
  obtain ⟨sp, args, bytes⟩ := CheckDomain.pub_facts relation.1
  exact ⟨h, sp.symm, fun i hi => (args i hi).symm, bytes.symm, (singleton_sym relation.2).symm⟩

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t

theorem After.pre {a t : State} (h : After a t) : (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) := by
  obtain ⟨s, start, result⟩ := h
  exact result.tracking.pre start.pre

theorem After.args {a t : State} (h : After a t) : ∀ i < 5, arg t i = arg a i := by
  obtain ⟨s, start, result⟩ := h
  intro i hi
  exact (result.tracking.args start.pre i hi).trans (start.args i hi)

theorem After.stack {a t : State} (h : After a t) : t.gpr .esp = a.gpr .esp := by
  obtain ⟨s, start, result⟩ := h
  exact result.tracking.stack.trans start.stack

theorem After.domain_eq {a t : State} (h : After a t) : domain t = domain a := by
  obtain ⟨s, start, result⟩ := h
  exact (result.tracking.domain_eq start.pre).trans start.domain

theorem After.public {a s t : State} (hs : After a s) (ht : After a t) :
    (Spec.Ffdh.checkDomainContract abi 172).pub s t := by
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes]
  refine ⟨hs.stack.trans ht.stack.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (domain s).map (·.toNat) = (domain t).map (·.toNat)
    rw [hs.domain_eq, ht.domain_eq]
  all_goals exact (hs.args _ (by decide)).trans (ht.args _ (by decide)).symm

end VG.Proof.Ffdh.X86.VettedValidation
