module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Entry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices

import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Spec.Rsa.Contract
/-! Exact public recognition is safe for every permitted input, including invalid domains. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Geometry.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open Cached

private theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat=x := by simp

def clobbers : List Reg := .x0::recordClobbers

def width (s : State) : Nat := policyWidth 4095 (s.gpr .x2).toNat (CheckDomain.cdDom s) Policy.groups

structure Result (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x3
  test : t.gpr .x10=BitVec.ofNat 64 (width s)-4095#64
  savedDomain : word t.mem (s.gpr .x3) (8*sDom)=s.gpr .x0
  savedLength : word t.mem (s.gpr .x3) (8*sDL)=s.gpr .x1
  savedKeyLength : word t.mem (s.gpr .x3) (8*sLen)=s.gpr .x2
  savedWords : word t.mem (s.gpr .x3) (8*sCtx)=s.gpr .x4
  frame : Outside (s.gpr .x3) 128 40 s.mem t.mem
  keep : Keep clobbers s t

theorem width_le (s : State) : width s≤4095 := by
  have bound (gs : List Policy.Group) : policyWidth 4095 (s.gpr .x2).toNat (CheckDomain.cdDom s) gs≤4095 := by
    induction gs with
    | nil => exact Nat.le_refl _
    | cons g gs ih =>
      unfold policyWidth
      split
      · exact Nat.min_le_left _ _
      · exact ih
  exact bound _

theorem recognize_ok {s : State} (g : Geometry s) :
    WP isa VG.Impl.Ffdh.AArch64.VettedValidation.recognize s (Result s) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.recognize
  rw [WP.seq_iff]
  refine WP.mono (entry_ok g.scratch g.room rfl) ?_
  rintro a ⟨⟨baseA,ptrA,countA,memA⟩,restA⟩
  have headers :=entryMemory_header s.mem (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4)
  have frameA : Outside (s.gpr .x3) 128 40 s.mem a.mem := by
    rw [memA];exact entryMemory_range _ _ _ _ _ _
  have recordsA :=g.records.after_belowBits frameA restA (by decide)
  have sourceA :=g.source.after_outside frameA restA g.outside
  rw [WP.seq_iff]
  refine WP.mono (policyLoop_ok (g.scratch.congr restA.wr) g.room baseA sourceA recordsA
    (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape)
    (by have :=g.small;omega) (by have :=g.large;omega)
    (by rw [memA];exact headers.1)
    (by rw [memA];simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range,ofNat_toNat64] using headers.2.1)
    (by rw [memA];simpa only [ofNat_toNat64] using headers.2.2.1)
    (by rw [memA];exact headers.2.2.2.2) (by decide) ptrA countA (by decide) (by decide)) ?_
  rintro b ⟨bitsB,frameB,restB⟩
  have baseB :=(restB.gpr .x0 (by simp [recordClobbers])).trans baseA
  have headerB (i : Nat) (hi : i<32) (different : i≠sBits) :
      word b.mem (s.gpr .x3) (8*i)=word a.mem (s.gpr .x3) (8*i) :=
    header_other frameB (by decide) hi different
  refine WP.mono (WP.keep [.x10] (Q:=fun t =>t.gpr .x10=BitVec.ofNat 64 (width s)-4095#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
  · brun [baseB,hdr_enc (show sBits<32 by decide),((g.scratch.congr restA.wr).congr restB.wr).ld (d:=8*sBits) (by unfold sBits;have :=g.room;omega),
      bitsB,width]
  · rintro t ⟨⟨testT,memT⟩,restT⟩
    refine ⟨(restT.gpr .x0 (by simp)).trans baseB,testT,?_,?_,?_,?_,?_,?_⟩
    · rw [memT,headerB sDom (by decide) (by decide),memA];exact headers.1
    · rw [memT,headerB sDL (by decide) (by decide),memA];exact headers.2.1
    · rw [memT,headerB sLen (by decide) (by decide),memA];exact headers.2.2.1
    · rw [memT,headerB sCtx (by decide) (by decide),memA];exact headers.2.2.2.1
    · rw [memT];exact frameA.trans (frameB.mono (by decide) (by decide))
    · exact ((restA.trans restB).trans restT).mono (by
        intro r hr
        simp only [List.mem_append] at hr
        rcases hr with (hr|hr)|hr
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl <;> decide
        · exact List.mem_cons_of_mem _ hr
        · have same : r= .x10 := by simpa using hr
          subst r
          decide)


end VG.Proof.Ffdh.AArch64.VettedValidation
