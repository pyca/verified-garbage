import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem hintNorm_eq : Impl.MlDsa.AArch64.Optimized.Response.hintNorm=
    .seq (.block hintInit) (.seq
      (.seq (.block [.movz .x .x10 16 0])
        (.loop (.block (hintBody++advance [.x0,.x1,.x2])) (.nonzero .x .x10)))
      (.block hintFinish)) := by rfl

/-- Full measured hint helper, including all failure-path writes and the packed return. -/
theorem hintNorm_machine (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa Impl.MlDsa.AArch64.Optimized.Response.hintNorm s fun t =>
      let d := hintRun s.mem ((s.gpr .x3).setWidth 32) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64
      Keep [.x0,.x1,.x2,.x9,.x10] s t ∧ t.mem=d.mem ∧
      t.gpr .x0=hintFinishValue d.counts d.flags := by
  rw [hintNorm_eq]
  apply WP.seq
  refine WP.mono (hintInit_ok s) fun a ⟨hka,hr,hcount,hflag⟩ => ?_
  have ka := setup_keep hka (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcounter,hmem⟩,hkb⟩,hvb⟩ => ?_
  have hrb : HintReady ((s.gpr .x3).setWidth 32) b :=
    hr.frame (rs:=[]) (by intro r _; exact congrFun hvb r) (by simp)
  refine WP.mono (hintLoop_ok hrb hcounter (by rw [hvb,hflag]) (by rw [hvb,hcount]) ?_ ?_ ?_ ?_)
    fun c ⟨hkc,_,_,_,_,hcm,hcf,hcc⟩ => ?_
  · intro off ho
    simpa only [hkb.rd,hkb.wr,hkb.get .x0 (by decide),hka.rd,hka.wr,hka.gpr .x0 (by decide)] using ha off ho
  · intro off ho
    simpa only [hkb.rd,hkb.wr,hkb.get .x1 (by decide),hka.rd,hka.wr,hka.gpr .x1 (by decide)] using hb off ho
  · intro off ho
    simpa only [hkb.wr,hkb.get .x0 (by decide),hka.wr,hka.gpr .x0 (by decide)] using hw off ho
  · intro off ho
    simpa only [hkb.rd,hkb.wr,hkb.get .x2 (by decide),hka.rd,hka.wr,hka.gpr .x2 (by decide)] using hh off ho
  · refine WP.mono (hintFinish_ok c) fun t ⟨⟨⟨hv,hm⟩,hkt⟩,_⟩ => ?_
    have hp0 : b.gpr .x0=s.gpr .x0 := (hkb.get .x0 (by decide)).trans (hka.gpr .x0 (by decide))
    have hp1 : b.gpr .x1=s.gpr .x1 := (hkb.get .x1 (by decide)).trans (hka.gpr .x1 (by decide))
    have hp2 : b.gpr .x2=s.gpr .x2 := (hkb.get .x2 (by decide)).trans (hka.gpr .x2 (by decide))
    refine ⟨(((ka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hm,hcm,hmem,hka.mem,hp0,hp1,hp2]
    · rw [hv,hcc,hcf,hmem,hka.mem,hp0,hp1,hp2]

end VG.Proof.MlDsa.AArch64.Optimized.Response
