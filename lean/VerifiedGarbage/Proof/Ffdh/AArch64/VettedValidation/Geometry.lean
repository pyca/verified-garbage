module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! The existing domain-check ABI supplies the recognizer's buffer geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open Cached

structure Geometry (s : State) : Prop where
  small : 64≤(s.gpr .x2).toNat
  large : (s.gpr .x2).toNat≤1024
  shape : (s.gpr .x1).toNat=2*(s.gpr .x2).toNat ∨ (s.gpr .x1).toNat=3*(s.gpr .x2).toNat
  scratch : Scr s (s.gpr .x3) ((s.gpr .x4).toNat*8)
  room : 256≤(s.gpr .x4).toNat*8
  source : Source (s.gpr .x0) (CheckDomain.cdDom s) s
  outside : ∀ i<(CheckDomain.cdDom s).length,168≤ofs (s.gpr .x3) (s.gpr .x0+BitVec.ofNat 64 i)
  records : PolicyTableAt (s.gpr .x3) (s.syms Policy.tableSym) Policy.groups s

theorem geometry {s : State} (h : pre s) : Geometry s := by
  obtain ⟨hp,constants⟩:=h
  simp only [CheckDomain.cdPre,stripConsts_gpr,stripConsts_wr] at hp
  obtain ⟨rd,wr,disjoint,domainWrap,scratchWrap,⟨small,large⟩,shape,length⟩:=hp
  change (s.gpr .x1).toNat=2*(s.gpr .x2).toNat ∨ (s.gpr .x1).toNat=3*(s.gpr .x2).toNat at shape
  change s.rd.take (s.rd.length-Policy.tableConsts.length)=[⟨s.gpr .x0,(s.gpr .x1).toNat⟩] at rd
  have member : (⟨s.gpr .x0,(s.gpr .x1).toNat⟩ : Region)∈s.rd := by
    apply List.mem_of_mem_take
    rw [rd];simp
  have scratch : Scr s (s.gpr .x3) ((s.gpr .x4).toNat*8) :=
    Scr.of_mem (by rw [wr];simp) scratchWrap
  have room : 256≤(s.gpr .x4).toNat*8 := by
    unfold Spec.Rsa.scratchWords at length
    omega
  have src :=src_of_region (List.mem_append_left s.wr member) (by omega) disjoint
  refine ⟨small,large,shape,scratch,room,src_source src,?_,policyConsts_table constants scratch room⟩
  intro i hi
  have bound :=src.out i hi
  omega

end VG.Proof.Ffdh.AArch64.VettedValidation
