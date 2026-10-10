import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked
import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintNorm
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField

/-! ## From `ResponseHintOnes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem hintAt_original (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) (hh : (pR p).Disjoint (pR h))
    {j e : Nat} (hj : j<64) (he : e<4) :
    hintAt B (hintRun m B p a h j).mem p a h j e=
      hintWord B (reduceWord (coeffAt m a (4*j+e))+coeffAt m p (4*j+e)) (coeffAt m h (4*j+e)) := by
  rw [hintAt_coeff _ _ _ _ _ _ he,
    hintRun_prefix m p a h B hd hh (by omega) (4*j+e) (by omega),ite_eq_right (by omega)]
  have fa := coeffAt_frame (hintRun_frame m p a h B (j:=j) (by omega))
    (by simpa using hd.symm) (show 4*j+e<n by change 4*j+e<256; omega)
  have fh := coeffAt_frame (hintRun_frame m p a h B (j:=j) (by omega))
    (by simpa using hh.symm) (show 4*j+e<n by change 4*j+e<256; omega)
  rw [fa,fh]

theorem hintCount_next (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) :
    hintCount m B p a h (j+1)=hintCount m B p a h j+
      (hintAt B (hintRun m B p a h j).mem p a h j 0).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 1).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 2).toNat+
      (hintAt B (hintRun m B p a h j).mem p a h j 3).toNat := by
  simp only [hintCount,hintLaneCount]
  omega

theorem hintCount_ones (m : Mem) (B : BitVec 32) (p a h : Addr) (out : Vector Bool n)
    (hd : (pR p).Disjoint (pR a)) (hh : (pR p).Disjoint (pR h))
    (ho : ∀k<256,(hintWord B (reduceWord (coeffAt m a k)+coeffAt m p k) (coeffAt m h k)).toNat=out[k]!.toNat) :
    hintCount m B p a h 64=hintOnes [out] := by
  have hi : ∀j≤64,hintCount m B p a h j=VG.Proof.MlDsa.Round.onesTo out (4*j) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [hintCount_next,ih (by omega)]
      have lane (e : Nat) (he : e<4) :
          (hintAt B (hintRun m B p a h j).mem p a h j e).toNat=out[4*j+e]!.toNat := by
        rw [hintAt_original m B p a h hd hh (by omega) he,ho _ (by omega)]
      rw [lane 0 (by decide),lane 1 (by decide),lane 2 (by decide),lane 3 (by decide)]
      rw [show 4*(j+1)=((4*j+1)+1)+1+1 by omega]
      rw [VG.Proof.MlDsa.Round.onesTo_succ,VG.Proof.MlDsa.Round.onesTo_succ,
        VG.Proof.MlDsa.Round.onesTo_succ,VG.Proof.MlDsa.Round.onesTo_succ]
      simp only [Nat.add_zero]
  rw [hi 64 (by decide),VG.Proof.MlDsa.Round.hintOnes_onesTo]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseHintValid.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem hintFailure_false (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) :
    hintFailure m B p a h 64=false ↔ ∀k<256,hintNormTest m a B k := by
  unfold hintFailure
  simp only [Bool.or_eq_false_iff]
  rw [hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide)]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ k hk
    have he : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by omega
    rcases he with he | he | he | he
    · simpa only [show 4*(k/4)+0=k by omega] using h0 (k/4) (by omega)
    · simpa only [show 4*(k/4)+1=k by omega] using h1 (k/4) (by omega)
    · simpa only [show 4*(k/4)+2=k by omega] using h2 (k/4) (by omega)
    · simpa only [show 4*(k/4)+3=k by omega] using h3 (k/4) (by omega)
  · intro h
    exact ⟨⟨⟨fun i hi => h _ (by omega),fun i hi => h _ (by omega)⟩,
      fun i hi => h _ (by omega)⟩,fun i hi => h _ (by omega)⟩

theorem hintFailure_field (m : Mem) (B : Nat) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) (hB : 1≤B) (hB' : B≤524288)
    (hr : ∀k<256,-8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<2*8380417) :
    hintFailure m (BitVec.ofNat 32 B) p a h 64=false ↔
      ∀k<256,normZq (ofInt (coeffAt m a k).toInt)<B := by
  rw [hintFailure_false m _ p a h hd]
  constructor
  · intro hv k hk
    exact (hintNormTest_field hB hB' (hr k hk).1 (hr k hk).2).mp (hv k hk)
  · intro hv k hk
    exact (hintNormTest_field hB hB' (hr k hk).1 (hr k hk).2).mpr (hv k hk)

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseHintLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def hintBody : List Instr := [0,16,32,48].flatMap (hintGroup)

theorem hintBody_ok {B : BitVec 32} {s : State} {m : Mem} {p a l : Addr} {u : Nat}
    (hr : HintReady B s) (hm : s.mem=(hintRun m B p a l (4*u)).mem) (hf : s.v .v31=(hintRun m B p a l (4*u)).flags)
    (hcount : s.v .v30=(hintRun m B p a l (4*u)).counts)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=l+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hl : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block hintBody) s fun t =>
      StepKeep [.v0,.v2,.v3,.v4,.v6,.v30,.v31] s t ∧ HintReady B t ∧
      t.mem=(hintRun m B p a l (4*(u+1))).mem ∧ t.v .v31=(hintRun m B p a l (4*(u+1))).flags ∧ t.v .v30=(hintRun m B p a l (4*(u+1))).counts := by
  let I := fun i t => StepKeep [.v0,.v2,.v3,.v4,.v6,.v30,.v31] s t ∧ HintReady B t ∧
    t.mem=(hintRun m B p a l (4*u+i)).mem ∧ t.v .v31=(hintRun m B p a l (4*u+i)).flags ∧ t.v .v30=(hintRun m B p a l (4*u+i)).counts
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf,hcount⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (hintGroup (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags,hcounts⟩
    refine WP.mono (hintGroup_step hi hready hmem hflags hcounts
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ((hk.keep.get .x2).trans h2) ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv,hcv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x2] using hl i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_,?_⟩
      · rw [show 4*u+(i+1)=4*u+i+1 by omega,hintRun]
        with_reducible exact hmv
      · rw [show 4*u+(i+1)=4*u+i+1 by omega,hintRun]
        with_reducible exact hfv
      · rw [show 4*u+(i+1)=4*u+i+1 by omega,hintRun]
        with_reducible exact hcv
  have h := fourGroups_ok (hintGroup) I hinit hstep
  simpa only [I,hintBody,show 4*u+4=4*(u+1) by omega] using h

theorem hintLoop_ok {B : BitVec 32} {s : State} (hr : HintReady B s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0) (hcount : s.v .v30=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (hintBody++advance [.x0,.x1,.x2])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x2,.x10] s t ∧ HintReady B t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧ t.gpr .x2=s.gpr .x2+1024 ∧
      t.mem=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.v .v31=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags ∧
      t.v .v30=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).counts := by
  let I := fun u t => Keep [.x0,.x1,.x2,.x10] s t ∧ HintReady B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (64*u) ∧
    t.mem=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).mem ∧
    t.v .v31=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).flags ∧
    t.v .v30=(hintRun s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).counts
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,h2,hm,hf,hcounts⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (hintBody_ok hready hm hf hcounts h0 h1 h2 ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv,hcv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact ha _ (by omega)
    · intro i hi
      simp only [hk.rd,hk.wr,h1,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hb _ (by omega)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega)
    · intro i hi
      simp only [hk.rd,hk.wr,h2,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hl _ (by omega)
    · refine WP.mono (advance3_ok v) fun w ⟨⟨⟨hw0,hw1,hw2,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,?_,hwm.trans hmv,?_,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by intro r _; exact congrFun hvw r) (by simp)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw2,hv.keep.get .x2,h2,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hvw,hcv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,by simp,rfl,hf,hcount⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseHintMachine.lean` -/

section

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

end

/-! ## From `ResponseHintContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlKem.AArch64 (Keep)

theorem hintCount_bound (m : Mem) (B : BitVec 32) (p a h : Addr) : hintCount m B p a h 64≤256 := by
  have h0 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=0) (by decide)
  have h1 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=1) (by decide)
  have h2 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=2) (by decide)
  have h3 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=3) (by decide)
  rw [hintRun_count_value _ _ _ _ _ (by decide) (by decide)] at h0 h1 h2 h3
  unfold hintCount
  omega

/-- Caller-facing exact output: low 32 bits count hints, high 32 bits validate ct0.
Rejected inputs still execute all coefficient writes and preserve the same frame. -/
theorem hintNorm_ok (s : State) (B : Nat) (out : Vector Bool n)
    (hB : 1≤B) (hB' : B≤524288) (hbreg : (s.gpr .x3).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hd : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)))
    (he : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)))
    (hr : ∀k<256,-8380417<(coeffAt s.mem (s.gpr .x1) k).toInt ∧
      (coeffAt s.mem (s.gpr .x1) k).toInt<2*8380417)
    (ho : ∀k<256,hintWord (BitVec.ofNat 32 B)
      (reduceWord (coeffAt s.mem (s.gpr .x1) k)+coeffAt s.mem (s.gpr .x0) k)
      (coeffAt s.mem (s.gpr .x2) k)=BitVec.ofNat 32 out[k]!.toNat) :
    WP isa Impl.MlDsa.AArch64.Optimized.Response.hintNorm s fun t =>
      Keep [.x0,.x1,.x2,.x9,.x10] s t ∧ Frame [pR (s.gpr .x0)] s.mem t.mem ∧
      HintIs t.mem (s.gpr .x0) 1 [out] ∧
      (t.gpr .x0).toNat%4294967296=hintOnes [out] ∧
      ((t.gpr .x0).toNat/4294967296=1 ↔
        ∀k<256,normZq (ofInt (coeffAt s.mem (s.gpr .x1) k).toInt)<B) ∧
      (t.gpr .x0).toNat/4294967296≤1 := by
  refine WP.mono (hintNorm_machine s ha hb hh hw) fun t ⟨hk,hm,hv⟩ => ?_
  simp only [hbreg] at hm hv
  have hc := hintCount_bound s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  have hcval := hintCount_ones s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) out hd he
    (by intro k hk; rw [ho k hk,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := out[k]!.toNat_le; omega)])
  have hret := hintRun_packed_value s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (j:=64) (by decide)
  rw [hcval] at hc hret
  have hvalid := hintFailure_field s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) hd hB hB' hr
  refine ⟨hk,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact hintRun_frame _ _ _ _ _ (by decide)
  · apply VG.Proof.MlDsa.Round.hintIs_of_toNat
    intro k hk
    rw [hm,hintRun_coeff _ _ _ _ _ hd he hk,ho k hk]
    rfl
  · rw [hv,hret]; split <;> omega
  · rw [hv,hret]
    cases hf : hintFailure s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64
    · simp only [hf,Bool.false_eq_true,ite_false] at *
      exact iff_of_true (by omega) (hvalid.mp trivial)
    · simp only [hf,ite_true] at *
      exact iff_of_false (by omega) (by intro hn; have := hvalid.mpr hn; contradiction)
  · rw [hv,hret]; split <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
