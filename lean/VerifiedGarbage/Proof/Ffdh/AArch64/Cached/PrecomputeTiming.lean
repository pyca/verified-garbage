module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInput
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeNativeTiming
import VerifiedGarbage.Proof.Framework.GetElem

/-! Public ABI inputs determine every initializer branch and address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem precomputePub_input {s t : State} (gs : PrecomputeGeometry s) (gt : PrecomputeGeometry t)
 (h : precomputePub s t) : precomputeInputPublic s gs=precomputeInputPublic t gt ∧ s.sp=t.sp :=by
 obtain ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6,symbol⟩:=h
 have bytes : precomputeDomain s=precomputeDomain t :=by
  have recover:=congrArg (List.map (BitVec.ofNat 8)) dom
  simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
 refine ⟨?_,sp⟩
 unfold precomputeInputPublic precomputeNativeParameters checkedParameters
 simp only [r0,r2,r3,r4,r5,r6,bytes,symbol]

theorem precompute_constantTime (M : Mont) : ConstantTime isa precomputePre precomputePub (Precompute.code M.mm) :=by
 intro s t ts tt u v hs ht hp es et
 let gs:=precompute_geometry hs
 let gt:=precompute_geometry ht
 have publicInfo:=precomputePub_input gs gt hp
 have first:=precompute_input_ready gs
 have second : PrecomputeReady (precomputeInputPublic s gs) t :=by
  rw [publicInfo.1];exact precompute_input_ready gt
 exact ((precomputeNative_ct M) _ _ _ _ _ _ ⟨precomputeInputPublic s gs,first,second,publicInfo.2⟩ es et).1

end VG.Proof.Ffdh.AArch64.Cached
