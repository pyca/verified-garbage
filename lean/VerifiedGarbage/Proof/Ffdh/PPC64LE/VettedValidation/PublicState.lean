module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Correct
import VerifiedGarbage.Proof.Framework.Contract

/-! Public anchors allow unrelated scratch contents and link-register values. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

def publicRegs : List Reg := [.r3, .r4, .r5, .r6, .r7]

structure Start (a s : State) : Prop where
  pre : contract.pre s
  regs : ∀ r ∈ publicRegs, s.gpr r = a.gpr r
  domain : domain s = domain a
  symbol : s.syms tableSym = a.syms tableSym
  sp : s.sp = a.sp

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], s.syms c.1 = t.syms c.1) :
    s.syms name = t.syms name := h (name, words) List.mem_cons_self

theorem start_of_pub {a s : State} (hs : contract.pre s) (hp : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi).pub a s ∧
      ∀ c ∈ tableConsts, a.syms c.1 = s.syms c.1 := pub_consts.mp hp
  have symbols := singleton_sym (name := tableSym) (words := VG.Impl.Ffdh.VettedGroups.tableWords) relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at pubBase
  obtain ⟨sp, bytes, r3, r4, r5, r6, r7⟩ := pubBase
  refine ⟨hs, ?_, ?_, symbols.symm, sp.symm⟩
  · intro r hr
    simp only [publicRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r3.symm
    · exact r4.symm
    · exact r5.symm
    · exact r6.symm
    · exact r7.symm
  · have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
    simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] at byteEq
    exact byteEq.symm

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t ∧ t.sp = s.sp

theorem After.pre {a t : State} (h : After a t) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain t) := by
  obtain ⟨s, start, result, _⟩ := h
  exact result.pre start.pre

theorem After.regs {a t : State} (h : After a t) : ∀ r ∈ publicRegs, t.gpr r = a.gpr r := by
  obtain ⟨s, start, result, _⟩ := h
  intro r hr
  exact (result.keep.gpr (by revert r; decide)).trans (start.regs r hr)

theorem After.sp {a t : State} (h : After a t) : t.sp = a.sp := by
  obtain ⟨s, start, _, sp⟩ := h
  exact sp.trans start.sp

theorem After.domain_eq {a t : State} (h : After a t) : domain t = domain a := by
  obtain ⟨s, start, result, _⟩ := h
  unfold domain
  rw [result.mem, result.keep.gpr (r := .r3) (by decide), result.keep.gpr (r := .r4) (by decide)]
  exact start.domain

theorem After.public {a s t : State} (hs : After a s) (ht : After a t) :
    (Spec.Ffdh.checkDomainContract abi).pub s t := by
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs]
  refine ⟨hs.sp.trans ht.sp.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (domain s).map (·.toNat) = (domain t).map (·.toNat)
    rw [hs.domain_eq, ht.domain_eq]
  all_goals exact (hs.regs _ (by decide)).trans (ht.regs _ (by decide)).symm

end VG.Proof.Ffdh.PPC64LE.VettedValidation
