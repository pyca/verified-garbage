import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem addNorm_eq : VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm=
    .seq (.block addInit) (.seq (.seq (.block [.movz .x .x10 16 0])
      (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)))
      VG.Impl.MlDsa.AArch64.Optimized.Response.finish) := rfl

theorem addNorm_words_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      Keep [.x0,.x1,.x9,.x10] s t ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.gpr .x0=finishValue (zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  rw [addNorm_eq]
  apply WP.seq
  refine WP.mono (addInit_ok s) fun a ⟨hsa,hready,hzero⟩ => ?_
  have hka := setup_keep hsa (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcount,hmem⟩,hkb⟩,hvec⟩ => ?_
  have hksb := hka.trans hkb
  have hrb : ZReady ((b.gpr .x2).setWidth 32) b := by
    rw [hkb.get .x2,hka.get .x2]
    exact hready.frame (rs := []) (by simp) (fun r _=>congrFun hvec r)
  refine WP.mono (addLoop_ok hrb hcount (by rw [hvec,hzero]) ?_ ?_ ?_) fun c ⟨hkc,hrc,h0,h1,hmc,hfc⟩ => ?_
  · simpa only [hkb.rd,hkb.wr,hkb.get .x0,hka.rd,hka.wr,hka.get .x0] using ha
  · simpa only [hkb.rd,hkb.wr,hkb.get .x1,hka.rd,hka.wr,hka.get .x1] using hb
  · simpa only [hkb.wr,hkb.get .x0,hka.wr,hka.get .x0] using hw
  · refine WP.mono (finish_ok c) fun t ⟨⟨⟨hout,hmt⟩,hkt⟩,hvt⟩ => ?_
    refine ⟨((hksb.trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hmt,hmc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]
    · rw [hout,hfc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]

end VG.Proof.MlDsa.AArch64.Optimized.Response
