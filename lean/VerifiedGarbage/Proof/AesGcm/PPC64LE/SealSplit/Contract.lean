module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Prelude
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: the existing split-seal API with its untrusted scratch adapter.
/-! # The POWER8 split-seal scratch contract -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


def scratchContract : Contract isa :=
  Sig.scratchContract PPC64LE.abi Spec.Gcm.sealSplitSig "work" .u64 320
    (Spec.Gcm.sealSplitPre PPC64LE.abi.ptrBits) (Spec.Gcm.sealSplitPost PPC64LE.abi.ptrBits) true 112



theorem allocated_arg (s : State) (i : Nat) (hi : i<4) :
    (allocated 112 s).mem.readW ((allocated 112 s).sp+BitVec.ofNat 64 (208+8*i)) 64=stackArg s i := by
  change (s.mem.writeW (s.sp-112) s.sp).readW (s.sp-112+BitVec.ofNat 64 (208+8*i)) 64=stackArg s i
  rw [Mem.readW_writeW_sep
    ((Offset.disjoint_base (s.sp-112) (d := 208+8*i) (n := 8) (k := 8) (by omega) (by omega)).sep
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
  change s.mem.readW (s.sp-112+BitVec.ofNat 64 (208+8*i)) 64=
    s.mem.readW (s.sp+BitVec.ofNat 64 (32+8*(8+i))) 64
  congr 1
  have hn : 208+8*i=112+(32+8*(8+i)) := by omega
  rw [hn,BitVec.ofNat_add]
  change s.sp-112#64+(112#64+BitVec.ofNat 64 (32+8*(8+i)))=_
  rw [← BitVec.add_assoc,BitVec.sub_add_cancel]


theorem allocated_work (s : State) : Prelude.work (allocated 112 s)=stackArg s 3 :=
  allocated_arg s 3 (by decide)



def contextR (s : State) : Region := ⟨s.gpr .r3,256⟩
def nonceR (s : State) : Region := ⟨s.gpr .r5,(s.gpr .r6).toNat⟩
def aadR (s : State) : Region := ⟨s.gpr .r7,(s.gpr .r8).toNat⟩
def sourceR (s : State) : Region := ⟨s.gpr .r9,(s.gpr .r10).toNat⟩
def dataR (s : State) : Region := ⟨stackArg s 0,(stackArg s 1).toNat⟩
def tagR (s : State) : Region := ⟨stackArg s 2,16⟩
def workR (s : State) : Region := ⟨stackArg s 3,2560⟩
def argsR (s : State) : Region := ⟨s.sp+96,32⟩
def stackR (s : State) : Region := ⟨s.sp-112,112⟩

structure Layout (s : State) : Prop where
  spFit : 112≤s.sp.toNat ∧ s.sp.toNat+128≤2^64
  rd : s.rd=[contextR s,nonceR s,aadR s,sourceR s,argsR s]
  wr : s.wr=[dataR s,tagR s,workR s]
  dataApart : ∀ r ∈ [contextR s,nonceR s,aadR s,sourceR s], r.Disjoint (dataR s)
  tagApart : ∀ r ∈ [contextR s,nonceR s,aadR s,sourceR s,dataR s], r.Disjoint (tagR s)
  workApart : ∀ r ∈ [contextR s,nonceR s,aadR s,sourceR s,dataR s,tagR s], r.Disjoint (workR s)
  argsApart : ∀ r ∈ [dataR s,tagR s,workR s], r.Disjoint (argsR s)
  stackApart : ∀ r ∈ [contextR s,nonceR s,aadR s,sourceR s,dataR s,tagR s,workR s,argsR s],
    (stackR s).Disjoint r
  fits : ∀ r ∈ [contextR s,nonceR s,aadR s,sourceR s,dataR s,tagR s,workR s], r.base.toNat+r.len≤2^64
  rounds : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14
  bound : (s.gpr .r10).toNat≤(stackArg s 1).toNat


theorem layout_pre (s : State) (hs : scratchContract.pre s) : Layout s := by
  sig_eval [scratchContract,Sig.scratchContract,Sig.withScratch,Curry.withScratch,Curry.app,Spec.Gcm.sealSplitSig,
    Spec.Gcm.sealSplitPre,PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop,stackBelow] at hs
  obtain ⟨hsp,hcap,hrd,hwr,hkd,hkt,hkw,hnd,hnt,hnw,had,hat,haw,hsd,hst,hsw,hdt,hdw,hda,htw,hta,hwa,
    hfctx,hfn,hfa,hfs,hfd,hft,hfw,hfargs,fc,fn,fa,fs,fd,ft,fw,hnr,hbound⟩ := hs
  refine ⟨⟨hsp,hcap⟩,hrd,hwr,?_,?_,?_,?_,?_,?_,hnr,hbound⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hkd,hnd,had,hsd]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hkt,hnt,hat,hst,hdt]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hkw,hnw,haw,hsw,hdw,htw]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hda,hta,hwa]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hfctx,hfn,hfa,hfs,hfd,hft,hfw,hfargs]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fc,fn,fa,fs,fd,ft,fw]


theorem shifted_input (s : State) (off : Nat) (ho : 112≤off) :
    (allocated 112 s).sp+BitVec.ofNat 64 off=s.sp+BitVec.ofNat 64 (off-112) := by
  change s.sp-112#64+BitVec.ofNat 64 off=_
  rw [← Offset.ofNat_sub_ofNat ho]
  bv_omega


theorem prelude_config (s : State) (hs : scratchContract.pre s) : Prelude.Config (allocated 112 s) := by
  have lay := layout_pre s hs
  refine ⟨?_,?_,?_,?_⟩
  · intro off ho
    have hb : 208≤off ∧ off≤232 := by
      simp only [Prelude.readOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> omega
    rw [shifted_input s off (by omega)]
    change InRegions (s.rd++(frameR 112 s::s.wr)) (s.sp+BitVec.ofNat 64 (off-112)) 8
    rw [lay.rd]
    exact ⟨argsR s,List.mem_append_left _ (by simp),
      Offset.contains _ (d := off-112) (n := 8) (e := 96) (k := 32) (by omega) (by omega) (by decide)⟩
  · intro off ho
    have hb : off=96 ∨ off=104 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using ho
    change InRegions (frameR 112 s::s.wr) (s.sp-112#64+BitVec.ofNat 64 off) 8
    exact ⟨frameR 112 s,List.mem_cons_self,
      Offset.contains _ (d := off) (n := 8) (e := 32) (k := 80) (by omega) (by omega) (by decide)⟩
  · rw [allocated_work]
    change Covers [workR s] (frameR 112 s::s.wr)
    rw [lay.wr]
    exact Covers.of_mem (by simp)
  · intro off ho
    rw [allocated_work]
    by_cases hw : off∈[96,104]
    · have hb : off=96 ∨ off=104 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hw
      exact (lay.stackApart (workR s) (by simp)).symm.sub_right
        (Offset.sub_base _ (d := off) (n := 8) (k := 112) (by omega))
    · have hread : off∈Prelude.readOffsets := by
        simp only [Prelude.argOffsets,List.mem_append] at ho
        exact ho.resolve_left hw
      have hb : 208≤off ∧ off≤232 := by
        simp only [Prelude.readOffsets,List.mem_cons,List.not_mem_nil,or_false] at hread
        rcases hread with rfl | rfl | rfl | rfl <;> omega
      rw [shifted_input s off (by omega)]
      exact (lay.argsApart (workR s) (by simp)).sub_right
        (Offset.sub _ (d := off-112) (n := 8) (e := 96) (k := 32) (by omega) (by omega))

end VG.Proof.AesGcm.PPC64LE.SealSplit
