module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The context and original stack arguments survive every controller and callee write. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem KeyInput.context_frame {p : KeyPublic} {s : State} (h : KeyInput p s) {m m' : Mem}
 (hf : Frame (KeyInput.changes s) m m') :
 Spec.Rsa.wordsAt m' p.ctx p.ctxLen=Spec.Rsa.wordsAt m p.ctx p.ctxLen :=by
 rw [←h.2]
 unfold Spec.Rsa.wordsAt
 apply List.map_congr_left
 intro i hi
 apply hf.readW (r:=inContext s)
 · have inside : i<(stackArg s 6).toNat :=List.mem_range.mp hi
   have size:=h.nowrap (r:=inContext s) (by simp [inReads])
   change (stackArg s 5).toNat+(stackArg s 6).toNat*8≤2^64 at size
   exact Offset.contains_base _ (by omega) (by omega)
 · exact h.read_disjoint (by simp [inReads])
 · decide

theorem KeyInput.argument_frame {p : KeyPublic} {s : State} (h : KeyInput p s) {m m' : Mem}
 (hf : Frame (KeyInput.changes s) m m') (j : Nat) (hj : j<7) :
 m'.readW (s.sp+BitVec.ofNat 64 (8*j)) 64=m.readW (s.sp+BitVec.ofNat 64 (8*j)) 64 :=by
 apply hf.readW (r:=inArgs s)
 · simp only [inArgs,stackArgAddr,Nat.mul_zero,BitVec.add_zero]
   exact Offset.contains_base _ (by omega) (by omega)
 · exact h.read_disjoint (by simp [inReads])
 · decide

theorem KeyLive.context_args {p : KeyPublic} {original s : State} {used keys scalars : Nat}
 (h : KeyLive p original used keys scalars s) :
 s.mem.readW (p.sp+40#64) 64=p.ctx ∧ s.mem.readW (p.sp+48#64) 64=BitVec.ofNat 64 p.ctxLen :=by
 have a:=h.input.argument_frame h.frame 5 (by decide)
 have b:=h.input.argument_frame h.frame 6 (by decide)
 rw [←h.input.sp_eq] at a b
 have ctx : original.mem.readW (p.sp+40#64) 64=p.ctx :=by
  have hctx :=congrArg KeyPublic.ctx h.input.2
  change stackArg original 5=p.ctx at hctx
  simpa only [stackArg,stackArgAddr,←h.input.sp_eq] using hctx
 have count : BitVec.ofNat 64 (stackArg original 6).toNat=BitVec.ofNat 64 p.ctxLen :=
  congrArg (BitVec.ofNat 64) (congrArg KeyPublic.ctxLen h.input.2)
 simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at count
 change original.mem.readW (original.sp+48#64) 64=BitVec.ofNat 64 p.ctxLen at count
 rw [←h.input.sp_eq] at count
 exact ⟨a.trans ctx,b.trans count⟩

theorem KeyLive.context_canonical {p : KeyPublic} {original s : State} {used keys scalars : Nat}
 (h : KeyLive p original used keys scalars s) :
 p.ctxLen=Spec.Ffdh.generationPrecomputedWords p.len ∧
 Spec.Ffdh.generationPrecompute p.len p.dom=some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) :=by
 rw [h.input.context_frame h.frame,←h.input.2]
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,count,canonical⟩:=h.input.1
 exact ⟨count,canonical⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
