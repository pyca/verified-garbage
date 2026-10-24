module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitialTimingState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The complete public table initializer uses fixed indices zero and one. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeInitial_ct (M : Mont) : RelCT isa (Two TableInitialReady) (Precompute.initial M.mm) (fun _ _ =>True) := by
 unfold Precompute.initial
 simp only [seqs]
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitialWorking)
  (two_map InitialPublic.p (fun _ _ h =>h.field) (fieldPowerInit_ct M))
  (fun _ _ h =>initialOne_working M h)) ?_
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitialWorking)
  (two_map InitialPublic.p (fun _ _ h =>⟨h.state.good,h.context⟩)
   (storeLiteral_ct (by decide : 6<8) (by decide : 0<2^16) (by taint_decide) (by taint_decide)))
  (fun _ _ h =>initialZero_stored h)) ?_
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=GeneratorLoaded)
  (two_map (fun q =>(⟨q.p,q.dom⟩ : GeneratorPublic)) (fun _ _ h =>⟨h.state.good,h.domain,h.length⟩) generatorLoad_ct)
  (fun _ _ h =>initialGenerator_loaded h)) ?_
 refine RelCT.seq (two_post (Ψ:=fun q s =>LiteralReady q.p s)
  (two_map (fun q =>fieldWs q.p) (fun q s h =>⟨q.p.mi,h.1.state.good,q.p.room⟩)
   (M.ct (by simp [MmUse,Public.aXm,Public.aX,Public.aR2]))) ?_)
  (two_map InitialPublic.p (fun _ _ h =>h)
   (storeLiteral_ct (by decide : 5<8) (by decide : 1<2^16) (by taint_decide) (by taint_decide)))
 intro q s h
 refine WP.mono (generator_basis M h.1.state h.2 q.reduced) ?_
 rintro t ⟨basis,frame,_⟩
 exact ⟨basis.good,(arrays_header frame (by decide)).trans h.1.context⟩

end VG.Proof.Ffdh.AArch64.Cached
