module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Prepare
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Frame
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: the split-seal call uses its existing public contract.
/-! # The framed split-seal callee -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE


theorem split_sdepth : sdepth Impl.AesGcm.PPC64LE.GatherSplit.sealCode=2800 := by
  decide +kernel

abbrev callContext (s : State) : Region := ⟨s.gpr .r3,256⟩
abbrev callNonce (s : State) : Region := ⟨s.gpr .r5,(s.gpr .r6).toNat⟩
abbrev callAad (s : State) : Region := ⟨s.gpr .r7,(s.gpr .r8).toNat⟩
abbrev callSource (s : State) : Region := ⟨s.gpr .r9,(s.gpr .r10).toNat⟩
abbrev callData (s : State) : Region := ⟨stackArg s 0,(stackArg s 1).toNat⟩
abbrev callTag (s : State) : Region := ⟨stackArg s 2,16⟩
abbrev callArgsRegion (s : State) : Region := ⟨stackArgAddr s 0,24⟩

structure CallLayout (s : State) : Prop where
  space : 2800≤s.sp.toNat
  capacity : s.sp.toNat+120≤2^64
  rd : s.rd=[callContext s,callNonce s,callAad s,callSource s,callArgsRegion s]
  wr : s.wr=[callData s,callTag s]
  dataApart : ∀ r∈[callContext s,callNonce s,callAad s,callSource s],r.Disjoint (callData s)
  tagApart : ∀ r∈[callContext s,callNonce s,callAad s,callSource s,callData s],r.Disjoint (callTag s)
  argsApart : ∀ r∈[callData s,callTag s],r.Disjoint (callArgsRegion s)
  stackApart : ∀ r∈[callContext s,callNonce s,callAad s,callSource s,callData s,callTag s,callArgsRegion s],
    (below s.sp 2800).Disjoint r
  fits : ∀ r∈[callContext s,callNonce s,callAad s,callSource s,callData s,callTag s],r.base.toNat+r.len≤2^64
  rounds : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14
  bound : (s.gpr .r10).toNat≤(stackArg s 1).toNat


theorem call_pre {s : State} (h : CallLayout s) :
    (Proof.Gcm.sealSplitContract PPC64LE.abi 2800).pre s := by
  have cd := h.dataApart (callContext s) (by simp)
  have nd := h.dataApart (callNonce s) (by simp)
  have ad := h.dataApart (callAad s) (by simp)
  have sd := h.dataApart (callSource s) (by simp)
  have ct := h.tagApart (callContext s) (by simp)
  have nt := h.tagApart (callNonce s) (by simp)
  have at_ := h.tagApart (callAad s) (by simp)
  have st := h.tagApart (callSource s) (by simp)
  have dt := h.tagApart (callData s) (by simp)
  have da := h.argsApart (callData s) (by simp)
  have ta := h.argsApart (callTag s) (by simp)
  have bc := h.stackApart (callContext s) (by simp)
  have bn := h.stackApart (callNonce s) (by simp)
  have ba := h.stackApart (callAad s) (by simp)
  have bs := h.stackApart (callSource s) (by simp)
  have bd := h.stackApart (callData s) (by simp)
  have bt := h.stackApart (callTag s) (by simp)
  have bargs := h.stackApart (callArgsRegion s) (by simp)
  have fc := h.fits (callContext s) (by simp)
  have fn := h.fits (callNonce s) (by simp)
  have fa := h.fits (callAad s) (by simp)
  have fs := h.fits (callSource s) (by simp)
  have fd := h.fits (callData s) (by simp)
  have ft := h.fits (callTag s) (by simp)
  sig_eval [Proof.Gcm.sealSplitContract,Proof.Gcm.sealSplitSig,Proof.Gcm.sealSplitPre,PPC64LE.abi,PPC64LE.argRegs,
    stackArg,stackArgAddr,List.getD,List.range,List.range.loop,stackBelow]
  exact ⟨h.space,h.capacity,h.rd,h.wr,cd,ct,nd,nt,ad,at_,sd,st,dt,da,ta,
    bc,bn,ba,bs,bd,bt,bargs,fc,fn,fa,fs,fd,ft,h.rounds,h.bound⟩


theorem call_post {s z : State} (h : (Proof.Gcm.sealSplitContract PPC64LE.abi 2800).post s z)
    (hR : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14)
    (hb : (s.gpr .r10).toNat≤(stackArg s 1).toNat) :
    Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat)
        (Spec.Gcm.ctxH s.mem (s.gpr .r3)) 16 (Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat ++
          (Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).drop (s.gpr .r10).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (Spec.Aes.bytesAt z.mem (stackArg s 0) (stackArg s 1).toNat,Spec.Aes.bytesAt z.mem (stackArg s 2) 16) := by
  sig_post [Proof.Gcm.sealSplitContract,Proof.Gcm.sealSplitSig,Proof.Gcm.sealSplitPost,PPC64LE.abi,PPC64LE.argRegs,
    stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at h
  exact h hR hb


theorem call_pub {s t : State}
    (hp : s.gpr .r3=t.gpr .r3 ∧ s.gpr .r4=t.gpr .r4 ∧ s.gpr .r5=t.gpr .r5 ∧ s.gpr .r6=t.gpr .r6 ∧
      s.gpr .r7=t.gpr .r7 ∧ s.gpr .r8=t.gpr .r8 ∧ s.gpr .r9=t.gpr .r9 ∧ s.gpr .r10=t.gpr .r10 ∧
      s.sp=t.sp ∧ stackArg s 0=stackArg t 0 ∧ stackArg s 1=stackArg t 1 ∧ stackArg s 2=stackArg t 2) :
    (Proof.Gcm.sealSplitContract PPC64LE.abi 2800).pub s t := by
  obtain ⟨g3,g4,g5,g6,g7,g8,g9,g10,hsp,a0,a1,a2⟩ := hp
  sig_pub [Proof.Gcm.sealSplitContract,Proof.Gcm.sealSplitSig,PPC64LE.abi,PPC64LE.argRegs,
    List.range,List.range.loop]
  sig_reduce [Proof.Gcm.sealSplitContract,Proof.Gcm.sealSplitSig,PPC64LE.abi,PPC64LE.argRegs,
    List.getD,List.range,List.range.loop]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.AesGcm.PPC64LE.GatherSplit
