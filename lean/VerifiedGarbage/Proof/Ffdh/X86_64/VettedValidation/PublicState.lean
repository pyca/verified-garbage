module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Restore
import VerifiedGarbage.Proof.Framework.Contract

/-! Shared public anchors for two imports with unrelated scratch contents. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

def publicRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

structure Start (a s : State) : Prop where
  pre : contract.pre s
  regs : ∀ r ∈ publicRegs, s.gpr r = a.gpr r
  domain : CheckDomain.cdDom s = CheckDomain.cdDom a
  symbol : s.syms tableSym = a.syms tableSym

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], s.syms c.1 = t.syms c.1) :
    s.syms name = t.syms name := h (name, words) List.mem_cons_self

theorem start_of_pub {a s : State} (hs : contract.pre s)
    (hp : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi 8).pub a s ∧
      ∀ c ∈ tableConsts, a.syms c.1 = s.syms c.1 := pub_consts.mp hp
  have symbols := singleton_sym (name := tableSym) (words := VG.Impl.Ffdh.VettedGroups.tableWords) relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq] at pubBase
  obtain ⟨rsp, bytes, rdi, rsi, rdx, rcx, r8⟩ := pubBase
  refine ⟨hs, ?_, ?_, symbols.symm⟩
  · intro r hr
    simp only [publicRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rdi.symm
    · exact rsi.symm
    · exact rdx.symm
    · exact rcx.symm
    · exact r8.symm
    · exact rsp.symm
  · have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
    simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] at byteEq
    exact byteEq.symm

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t

def Ready (a t : State) : Prop := ∃ s, Start a s ∧ Restored s t

theorem Ready.pre {a t : State} (h : Ready a t) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (plain t) := by
  obtain ⟨s, start, restored⟩ := h
  exact restored.pre start.pre

theorem Ready.public {a s t : State} (hs : Ready a s) (ht : Ready a t) :
    (Spec.Ffdh.checkDomainContract abi 8).pub s t := by
  obtain ⟨s0, startS, restoredS⟩ := hs
  obtain ⟨t0, startT, restoredT⟩ := ht
  have domainS := (restoredS.domain (geometry startS.pre)).trans startS.domain
  have domainT := (restoredT.domain (geometry startT.pre)).trans startT.domain
  have spS := (restoredS.keep.gpr (r := .rsp) (by decide)).trans (startS.regs .rsp (by decide))
  have spT := (restoredT.keep.gpr (r := .rsp) (by decide)).trans (startT.regs .rsp (by decide))
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq]
  refine ⟨spS.trans spT.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (CheckDomain.cdDom s).map (·.toNat) = (CheckDomain.cdDom t).map (·.toNat)
    rw [domainS, domainT]
  · exact (restoredS.args.1.trans (startS.regs .rdi (by decide))).trans
      (restoredT.args.1.trans (startT.regs .rdi (by decide))).symm
  · exact (restoredS.args.2.1.trans (startS.regs .rsi (by decide))).trans
      (restoredT.args.2.1.trans (startT.regs .rsi (by decide))).symm
  · exact (restoredS.args.2.2.1.trans (startS.regs .rdx (by decide))).trans
      (restoredT.args.2.2.1.trans (startT.regs .rdx (by decide))).symm
  · exact (restoredS.args.2.2.2.1.trans (startS.regs .rcx (by decide))).trans
      (restoredT.args.2.2.2.1.trans (startT.regs .rcx (by decide))).symm
  · exact (restoredS.args.2.2.2.2.trans (startS.regs .r8 (by decide))).trans
      (restoredT.args.2.2.2.2.trans (startT.regs .r8 (by decide))).symm

end VG.Proof.Ffdh.X86_64.VettedValidation
