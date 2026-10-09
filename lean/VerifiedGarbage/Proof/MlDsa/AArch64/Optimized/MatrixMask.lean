import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMaskInit

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem mask_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {a : Ptr} {N : Nat} (hpos : 0<N) (hN : N≤64)
    (hw : inB wbs a (64*N)=true) (hin : inB (rbs++wbs) a (64*N)=true)
    (hr : (s.gpr .x0).setWidth 32=0 ∨ (s.gpr .x0).setWidth 32=1) :
    WP isa (code a (16*N)) s fun t => PPostB S s t [(a,64*N)] ∧
      Keep [.x1,.x2,.x8,.x9] s t ∧ ∀i<16*N,coeffAt t.mem (pa s a) i=
        if (s.gpr .x0).setWidth 32=1 then coeffAt s.mem (pa s a) i else 0 := by
  have hcode : code a (16*N)=.seq (.block (setup a N)) (.loop (.block body) (.nonzero .x .x2)) := by
    simp only [code,setup,scalar,footer,Nat.mul_div_cancel_left _ (by decide : 0<16),List.append_assoc]
    rfl
  rw [hcode]
  apply WP.seq
  refine WP.mono (setup_ok (L.ptrBs hin) (by omega) hr) fun u ⟨hu,hp,hc,hv⟩ => ?_
  have hr' i (hi : i<4*N) : InRegions (u.rd++u.wr) (pa s a+BitVec.ofNat 64 (16*i)) 16 := by
    rw [hu.keep.rd,hu.keep.wr]
    exact VG.Proof.MlKem.AArch64.in_rd_wr (inRegions_sub (L.inW hw) (by omega) (by omega))
  have hw' i (hi : i<4*N) : InRegions u.wr (pa s a+BitVec.ofNat 64 (16*i)) 16 := by
    rw [hu.keep.wr]
    exact inRegions_sub (L.inW hw) (by omega) (by omega)
  have hi : LoopInv u u (pa s a) (resultMask s) N 0 :=
    ⟨by omega,Keep.refl _ _,fun _ _ => rfl,rfl,by simpa using hp,by simpa using hc,hv⟩
  refine WP.mono (loop_ok hi hpos hN hr' hw') fun t ht => ?_
  have hk : Keep [.x1,.x2,.x8,.x9] s t := (hu.keep.trans ht.keep).mono (by decide)
  have hm : t.mem=maskRun s.mem (pa s a) (resultMask s) (4*N) := by rw [ht.mem,hu.mem]
  have hf : Frame [⟨pa s a,64*N⟩] s.mem t.mem := by
    rw [hm]
    exact maskRun_frame _ _ _ (Nat.le_refl _) hN
  refine ⟨postB_of_keep hk (by decide) hf,hk,?_⟩
  intro i hi
  rw [hm]
  rcases hr with h | h
  · simp only [resultMask,h]
    exact maskRun_zero (by omega) i (by omega)
  · simp only [resultMask,h,ite_true,BoundedFour.maskRun_identity]

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
