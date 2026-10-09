import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

theorem maskOne_ok {s : State} {k : Nat} (hk : k<4) {b p : Addr}
    (hb : s.gpr .x19=b) (hp : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p)
    (hc : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256)
    (hr : ∀i<64,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>
      Keep [.x3,.x4,.x5,.x6] s t ∧
      (∀r,r∉[VReg.v0,.v1]→t.v r=s.v r) ∧Frame [polyR p] s.mem t.mem ∧
      (s.mem.readW (countAt b k) 64=0#64→t.mem=s.mem) ∧
      (s.mem.readW (countAt b k) 64≠0#64→∀i<256,coeffAt t.mem p i=0#32) := by
  change WP isa (.seq (.block (maskSetup k))
    (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5))) s _
  refine WP.seq (WP.mono (maskSetup_ok hk hb hc hx) fun a ⟨ha,hp',h5,hv⟩=>?_)
  let v:=outputMask (s.mem.readW (countAt b k) 64)
  have hi : MaskInv a a p v 0 := by
    refine ⟨by decide,Keep.refl _ _,fun _ _=>rfl,rfl,?_,h5,hv⟩
    change a.gpr .x3=p+0#64
    rw [BitVec.add_zero]
    exact hp'.trans hp
  refine WP.mono (maskLoop_ok hi (by decide)
    (fun i hi=>by rw [ha.keep.rd,ha.keep.wr]; exact hr i hi)
    (fun i hi=>by rw [ha.keep.wr]; exact hw i hi)) fun t ht=>?_
  refine ⟨(ha.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r h
    rw [ht.vec r (by simpa using fun he=>h (by simp [he])),ha.vec r (fun he=>h (by simp_all))]
  · rw [ht.mem,ha.mem]
    exact maskRun_frame _ _ _ (by decide)
  · intro hz
    rw [ht.mem,ha.mem]
    change maskRun s.mem p (outputMask _) 64=s.mem
    rw [outputMask,ite_eq_left hz,maskRun_identity]
  · intro hz i hi
    rw [ht.mem,ha.mem]
    change coeffAt (maskRun s.mem p (outputMask _) 64) p i=0#32
    rw [outputMask,ite_eq_right hz]
    exact maskRun_zero (by decide) i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
