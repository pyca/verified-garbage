module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptContract
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextView
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CheckedParameters
import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Stages
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The reviewed buffer layout supplies every native input, output, alias and context-read obligation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure AttemptGeometry (s : State) : Prop where
 small : 64≤(s.gpr .x6).toNat
 large : (s.gpr .x6).toNat≤1024
 shape : (s.gpr .x5).toNat=2*(s.gpr .x6).toNat ∨ (s.gpr .x5).toNat=3*(s.gpr .x6).toNat
 randLength : (stackArg s 0).toNat=(s.gpr .x6).toNat
 room : slot (((s.gpr .x6).toNat+7)/8) 8≤(stackArg s 2).toNat*8
 scratch : Scr s (stackArg s 1) ((stackArg s 2).toNat*8)
 stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8
 stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8
 domain : Src s (stackArg s 1) ((stackArg s 2).toNat*8) (s.gpr .x4) (attemptDomain s)
 random : Src s (stackArg s 1) ((stackArg s 2).toNat*8) (s.gpr .x7) (attemptRandom s)
 view : ContextView (stackArg s 1) ((stackArg s 2).toNat*8) (stackArg s 3) (stackArg s 4).toNat
  (s.gpr .x6).toNat (attemptDomain s) s
 checked : Spec.Ffdh.domainValid (s.gpr .x6).toNat (attemptDomain s)=true
 writeX : ∀ i<(s.gpr .x6).toNat,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 i) 1
 writeY : ∀ i<(s.gpr .x6).toNat,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 i) 1
 outsideX : ∀ i<(s.gpr .x6).toNat,(stackArg s 2).toNat*8≤ofs (stackArg s 1) (s.gpr .x0+BitVec.ofNat 64 i)
 outsideY : ∀ i<(s.gpr .x6).toNat,(stackArg s 2).toNat*8≤ofs (stackArg s 1) (s.gpr .x2+BitVec.ofNat 64 i)
 separateRand : ∀ i<(s.gpr .x6).toNat,∀ j<(s.gpr .x6).toNat,s.gpr .x7+BitVec.ofNat 64 i≠s.gpr .x0+BitVec.ofNat 64 j
 separateDomain : ∀ i<(attemptDomain s).length,(s.gpr .x6).toNat≤ofs (s.gpr .x0) (s.gpr .x4+BitVec.ofNat 64 i)
 separateContext : ∀ i<8*(stackArg s 4).toNat,(s.gpr .x6).toNat≤ofs (s.gpr .x0) (stackArg s 3+BitVec.ofNat 64 i)
 separateOutputs : ∀ i<(s.gpr .x6).toNat,(s.gpr .x6).toNat≤ofs (s.gpr .x2) (s.gpr .x0+BitVec.ofNat 64 i)

theorem attempt_geometry {s : State} (h : attemptPre s) : AttemptGeometry s :=by
 obtain ⟨spFits,rd,wr,dXY,dXD,dXR,dXS,dXC,dXA,dYD,dYR,dYS,dYC,dYA,dDS,dRS,dSC,dSA,
  wX,wY,wD,wR,wS,wC,⟨small,large⟩,shape,xLen,yLen,rLen,sLen,checked,canonical⟩:=h
 have scratch : Scr s (stackArg s 1) ((stackArg s 2).toNat*8) :=Scr.of_mem (by rw [wr];simp) wS
 have scrRoom : 128*(s.gpr .x6).toNat+256≤(stackArg s 2).toNat*8 :=by unfold Spec.Rsa.scratchWords at sLen;omega
 have dlen : (attemptDomain s).length=(s.gpr .x5).toNat :=by simp only [attemptDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 have readArgs (d : Nat) (fit : d+8≤40) : InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 d) 8 :=
  ⟨⟨s.sp,40⟩,by rw [rd];simp [stackArgAddr],Offset.contains_base _ fit (by omega)⟩
 refine ⟨small,large,shape,rLen,?_,scratch,readArgs 8 (by decide),readArgs 24 (by decide),
  src_of_region (by rw [rd];simp) (by omega) dDS,src_of_region (by rw [rd];simp) (by omega) dRS,
  ⟨canonical,?_,?_⟩,checked,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · dsimp only [slot,hdrBytes];omega
 · intro i hi
   exact ⟨⟨stackArg s 3,(stackArg s 4).toNat*8⟩,by rw [rd];simp,Offset.contains_base _ (by omega) (by omega)⟩
 · intro i hi
   exact out_scr dSC.symm (contains_byte _ (by omega) (by omega))
 · intro i hi
   exact ⟨⟨s.gpr .x0,(s.gpr .x1).toNat⟩,by rw [wr];simp,contains_byte _ (by omega) (by omega)⟩
 · intro i hi
   exact ⟨⟨s.gpr .x2,(s.gpr .x3).toNat⟩,by rw [wr];simp,contains_byte _ (by omega) (by omega)⟩
 · intro i hi
   exact out_scr dXS (contains_byte _ (by omega) (by omega))
 · intro i hi
   exact out_scr dYS (contains_byte _ (by omega) (by omega))
 · intro i hi j hj
   rw [xLen,rLen] at dXR
   rw [xLen] at wX
   rw [rLen] at wR
   exact VG.Proof.Ffdh.AArch64.GenerateKey.ne_of_disj dXR.symm wR wX hi hj
 · intro i hi
   rw [xLen] at dXD
   exact out_scr dXD.symm (contains_byte _ (by rw [dlen] at hi;exact hi) (by omega))
 · intro i hi
   rw [xLen] at dXC
   exact out_scr dXC.symm (contains_byte _ (by omega) (by omega))
 · intro i hi
   rw [xLen,yLen] at dXY
   exact out_scr dXY (contains_byte _ (by omega) (by omega))

end VG.Proof.Ffdh.AArch64.Cached
