import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Round

def lowArm (g : Nat) : Prog isa :=
  .seq (.block (lowInit g)) (.seq (.seq (.block [.movz .x .x10 16 0])
    (.loop (.block (lowBody g++advance [.x0,.x1,.x2])) (.nonzero .x .x10)))
    VG.Impl.MlDsa.AArch64.Optimized.Response.finish)

theorem subLowNorm_eq : VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm=
    VG.Impl.MlDsa.AArch64.Round.zext .x3 (VG.Impl.MlDsa.AArch64.Round.onGamma .x3 .x5 lowArm) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
  congr 1

theorem lowArm_words_ok {g B : Nat} (hg : IsG g) (hB : 1≤B) (s : State)
    (hbound : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (lowArm g) s fun t =>
      Keep [.x0,.x1,.x2,.x9,.x10] s t ∧
      t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.gpr .x0=finishValue (lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  unfold lowArm
  apply WP.seq
  refine WP.mono (lowInit_ok hg hB hbound) fun a ⟨hsa,hready,hzero⟩ => ?_
  have hka := setup_keep hsa (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcount,hmem⟩,hkb⟩,hvec⟩ => ?_
  have hksb := hka.trans hkb
  have hrb : LowReady g B b := hready.frame (rs:=[]) (fun r _=>congrFun hvec r) (by simp)
  refine WP.mono (lowLoop_ok hg hrb hcount (by rw [hvec,hzero]) ?_ ?_ ?_ ?_) fun c ⟨hkc,_,_,_,_,hmc,hfc⟩ => ?_
  · simpa only [hkb.rd,hkb.wr,hkb.get .x0,hka.rd,hka.wr,hka.get .x0] using ha
  · simpa only [hkb.rd,hkb.wr,hkb.get .x1,hka.rd,hka.wr,hka.get .x1] using hb
  · simpa only [hkb.wr,hkb.get .x0,hka.wr,hka.get .x0] using hw
  · simpa only [hkb.wr,hkb.get .x2,hka.wr,hka.get .x2] using hl
  · refine WP.mono (finish_ok c) fun t ⟨⟨⟨hout,hmt⟩,hkt⟩,_⟩ => ?_
    refine ⟨((hksb.trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hmt,hmc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]
    · rw [hout,hfc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]

theorem subLowNorm_words_ok {B : Nat} (s : State) (hg : IsG (arg32 s .x3)) (hB : 1≤B)
    (hbound : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s fun t =>
      Keep [.x0,.x1,.x2,.x3,.x5,.x9,.x10] s t ∧
      t.mem=(lowRun s.mem (arg32 s .x3) B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.gpr .x0=finishValue (lowRun s.mem (arg32 s .x3) B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  rw [subLowNorm_eq]
  apply zext_ok
  have hz := zextS_keep .x3 s
  refine onGamma_ok (by decide) (by rw [zextS_toNat]; exact hg) fun g hge a hka hma => ?_
  have he : g=arg32 s .x3 := by rw [zextS_toNat] at hge; exact hge.symm
  rw [he]
  have hks := hz.trans hka
  refine WP.mono (lowArm_words_ok hg hB a ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hmt,hout⟩ => ?_
  · rw [hks.get .x4 (by decide)]; exact hbound
  · simpa only [hks.rd,hks.wr,hks.get .x0 (by decide)] using ha
  · simpa only [hks.rd,hks.wr,hks.get .x1 (by decide)] using hb
  · simpa only [hks.wr,hks.get .x0 (by decide)] using hw
  · simpa only [hks.wr,hks.get .x2 (by decide)] using hl
  · refine ⟨(hks.trans hkt).mono,?_,?_⟩
    · rw [hmt,hma,zextS_mem,hks.get .x0 (by decide),hks.get .x1 (by decide),hks.get .x2 (by decide)]
    · rw [hout,hma,zextS_mem,hks.get .x0 (by decide),hks.get .x1 (by decide),hks.get .x2 (by decide)]

end VG.Proof.MlDsa.AArch64.Optimized.Response
