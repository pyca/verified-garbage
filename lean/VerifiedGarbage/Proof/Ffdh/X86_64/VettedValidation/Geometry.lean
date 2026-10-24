module

import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

/-! The existing parameter contract supplies the same buffers and two spare header words. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 8
def plain (s : State) := stripConsts tableConsts s

theorem pre_plain {s : State} (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (plain s) ∧ ConstsOk tableConsts 8 s :=
  pre_consts.mp h

theorem cd_pre {s : State} (h : contract.pre s) : CheckDomain.cdPre (plain s) := by
  have old := (pre_plain h).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at old
  sig_split old
  sig_reduce [CheckDomain.cdPre, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

structure Geometry (s : State) : Prop where
  scratch : Scr s (s.gpr .rcx) ((s.gpr .r8).toNat * 8)
  writable : (⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩ : Region) ∈ s.wr
  room : 144 ≤ (s.gpr .r8).toNat * 8
  read : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat
  shape : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨
    (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  lower : 64 ≤ (s.gpr .rdx).toNat
  upper : (s.gpr .rdx).toNat ≤ 1024
  separate : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint
    ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  returnSeparate : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  consts : ConstsOk tableConsts 8 s

theorem geometry {s : State} (h : contract.pre s) : Geometry s := by
  have cd := cd_pre h
  obtain ⟨rd, wr, sep, dfits, sfits, retDom, retScr, sizes, shape, space⟩ := cd
  refine ⟨Scr.of_mem ?_ sfits, ?_, ?_, ?_, shape, sizes.1, sizes.2, sep, retScr, (pre_plain h).2⟩
  · change (⟨(plain s).gpr .rcx, ((plain s).gpr .r8).toNat * 8⟩ : Region) ∈ (plain s).wr
    rw [wr]
    exact List.mem_cons_self
  · change (⟨(plain s).gpr .rcx, ((plain s).gpr .r8).toNat * 8⟩ : Region) ∈ (plain s).wr
    rw [wr]
    exact List.mem_cons_self
  · change Spec.Ffdh.pLenValid (s.gpr .rdx).toNat at sizes
    have low := sizes.1
    change Spec.Rsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r8).toNat at space
    simp only [Spec.Rsa.scratchWords] at space
    omega
  · obtain ⟨r, member, contains⟩ := (show InRegions ((plain s).rd ++ (plain s).wr)
        ((plain s).gpr .rdi) ((plain s).gpr .rsi).toNat from
      ⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_cons_self), Region.contains_self _ _⟩)
    refine ⟨r, ?_, contains⟩
    rcases List.mem_append.mp member with hr | hw
    · exact List.mem_append_left _ (List.mem_of_mem_take hr)
    · exact List.mem_append_right _ hw

end VG.Proof.Ffdh.X86_64.VettedValidation
