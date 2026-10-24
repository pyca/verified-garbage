module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeContract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CheckedParameters
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The reviewed initializer buffers and constant regions supply the native geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PrecomputeGeometry (s : State) : Prop where
 small : 64≤(s.gpr .x4).toNat
 large : (s.gpr .x4).toNat≤1024
 shape : (s.gpr .x3).toNat=2*(s.gpr .x4).toNat ∨ (s.gpr .x3).toNat=3*(s.gpr .x4).toNat
 count : (s.gpr .x1).toNat=3+34*(((s.gpr .x4).toNat+7)/8)
 room : slot (((s.gpr .x4).toNat+7)/8) 8≤(s.gpr .x6).toNat*8
 scratch : Scr s (s.gpr .x5) ((s.gpr .x6).toNat*8)
 context : Scr s (s.gpr .x0) ((s.gpr .x1).toNat*8)
 source : Src s (s.gpr .x5) ((s.gpr .x6).toNat*8) (s.gpr .x2) (precomputeDomain s)
 domainOutside : ∀ i<(precomputeDomain s).length,(s.gpr .x1).toNat*8≤ofs (s.gpr .x0) (s.gpr .x2+BitVec.ofNat 64 i)
 contextOutside : ∀ i<(s.gpr .x1).toNat*8,(s.gpr .x6).toNat*8≤ofs (s.gpr .x5) (s.gpr .x0+BitVec.ofNat 64 i)
 span : InRegions (s.rd++s.wr) (s.gpr .x2) (s.gpr .x4).toNat
 checked : Spec.Ffdh.domainValid (s.gpr .x4).toNat (precomputeDomain s)=true
 constants : ConstsOk Policy.tableConsts 0 s

theorem precompute_geometry {s : State} (h : precomputePre s) : PrecomputeGeometry s :=by
 obtain ⟨plain,constants⟩:=h
 simp only [precomputePlainPre,stripConsts_gpr,stripConsts_wr] at plain
 obtain ⟨rd,wr,dCD,dCS,dDS,wC,wD,wS,⟨small,large⟩,shape,count,sLen,checked⟩:=plain
 change s.rd.take (s.rd.length-Policy.tableConsts.length)=[⟨s.gpr .x2,(s.gpr .x3).toNat⟩] at rd
 change (s.gpr .x3).toNat=2*(s.gpr .x4).toNat ∨ (s.gpr .x3).toNat=3*(s.gpr .x4).toNat at shape
 have member : (⟨s.gpr .x2,(s.gpr .x3).toNat⟩ : Region)∈s.rd :=by
  apply List.mem_of_mem_take
  rw [rd];simp
 have scratch : Scr s (s.gpr .x5) ((s.gpr .x6).toNat*8) :=Scr.of_mem (by rw [wr];simp) wS
 have context : Scr s (s.gpr .x0) ((s.gpr .x1).toNat*8) :=Scr.of_mem (by rw [wr];simp) wC
 have countEq : (s.gpr .x1).toNat=3+34*(((s.gpr .x4).toNat+7)/8) :=by
  simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,Spec.Rsa.precomputedWords,
   Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Spec.Rsa.modulusWords] at count
  omega
 have room : slot (((s.gpr .x4).toNat+7)/8) 8≤(s.gpr .x6).toNat*8 :=by
  unfold Spec.Rsa.scratchWords at sLen
  dsimp only [slot,hdrBytes];omega
 have domLength : (precomputeDomain s).length=(s.gpr .x3).toNat :=by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 refine ⟨small,large,shape,countEq,room,scratch,context,src_of_region (List.mem_append_left _ member) (by omega) dDS,?_,?_,?_,checked,constants⟩
 · intro i hi
   exact out_scr dCD.symm (contains_byte _ (by rw [domLength] at hi;exact hi) (by omega))
 · intro i hi
   exact out_scr dCS (contains_byte _ hi (by omega))
 · refine ⟨⟨s.gpr .x2,(s.gpr .x3).toNat⟩,List.mem_append_left _ member,?_⟩
   have span :=Offset.contains_base (s.gpr .x2) (d:=0) (n:=(s.gpr .x4).toNat) (k:=(s.gpr .x3).toNat) (by omega) (by decide)
   simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using span

end VG.Proof.Ffdh.AArch64.Cached
