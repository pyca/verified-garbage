module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasisLoop
import VerifiedGarbage.Proof.Framework.Omega

/-! The public table completes exactly four tooth rounds. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure BasisLoopPublic where
 p : Parameters
 bits : 0<p.N ∧ p.N≤8192

def BasisLoopReady (q : BasisLoopPublic) (i : Nat) (s : State) : Prop := BasisState q.p (i+1) s

private theorem basisFlag : ∀ i<4,
 (BitVec.ofNat 64 (2^((i+1)+1))-32#64 !=0#64)=decide (i+1<4) := by decide +kernel

theorem precomputeBasisLoop_ct (M : Mont) : RelCT isa (Two fun q s =>BasisLoopReady q 0 s)
 (.loop (Precompute.basis M.mm) (.nonzero .x .x3)) (fun _ _ =>True) := by
 have hct : RelCT isa (Two fun (q : BasisLoopPublic × Fin 4) s =>BasisLoopReady q.1 q.2.val s)
  (Precompute.basis M.mm) (fun _ _ =>True) :=
  two_map (fun q =>(⟨q.1.p,q.2.val+1,by omega,by have :=q.2.isLt;omega,q.1.bits⟩ : BasisPublic))
   (fun _ _ h =>h) (precomputeBasis_ct M)
 have stepCt : RelCT isa (Two fun (q : BasisLoopPublic × Nat) s =>q.2<4 ∧ BasisLoopReady q.1 q.2 s)
  (Precompute.basis M.mm) (fun _ _ =>True) := by
  intro s t ts tt u v h es et
  obtain ⟨⟨q,i⟩,⟨hi,hs⟩,⟨_,ht⟩,sp⟩:=h
  exact hct _ _ _ _ _ _ ⟨(q,⟨i,hi⟩),hs,ht,sp⟩ es et
 have loop:=two_loop (cond:= .nonzero .x .x3) (Φ:=BasisLoopReady) (Ψ:=fun _ _ =>True)
  (fun _ : BasisLoopPublic =>4) stepCt (by
   intro q i s hi h
   refine WP.mono (precomputeBasis_ok M h (by omega : i+1<5)) ?_
   rintro t ⟨state,index,_,_⟩
   refine ⟨?_,fun _ =>state,fun _ =>trivial⟩
   rw [eval_nonzero,index]
   exact congrArg some (basisFlag i hi))
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨by decide,hs⟩,⟨by decide,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
