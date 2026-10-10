import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

/-! ## From `ResponseLowFlags.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def lowBad (m : Mem) (g : Nat) (p a : Addr) (B j e : Nat) : Bool :=
  decide (B≤normZq (ofInt (lowBits g (ofInt
    (((coeffAt m p (4*j+e)).toNat:Int)-(coeffAt m a (4*j+e)).toInt)))))

theorem lowOutput_current (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {j e : Nat} (hj : j<64) (he : e<4) :
    lowOutput g (lowRun m g B p a l j).mem p a j e=lowSigned m g p a (4*j+e) := by
  rw [lowOutput_coeff _ _ _ _ _ he]
  simp only [lowSigned,lowHigh,lowCanonical]
  rw [(lowRun_prefix m g B p a l hpl hap hal (by omega)).1 _ (by omega),ite_eq_right (by omega),
    lowRun_input (by omega) (by omega) hap hal]

theorem lowSigned_mask {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (m : Mem) (p a : Addr) (i : Nat) (ha : (coeffAt m p i).toNat<8380417)
    (hb : -8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    normMask (lowSigned m g p a i) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      maskWord (decide (B≤normZq (ofInt (lowBits g (ofInt (((coeffAt m p i).toNat:Int)-(coeffAt m a i).toInt)))))) := by
  rw [lowSigned,lowHigh,lowCanonical,subLow_norm hg ha hb.1 hb.2 hB hB']
  unfold maskWord
  split <;> rename_i h
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

theorem lowRun_flags (m : Mem) (g B : Nat) (p a l : Addr)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288)
    (ha : ∀i<256,(coeffAt m p i).toNat<8380417)
    (hb : ∀i<256,-8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    {j : Nat} (hj : j≤64) :
    ∀e<4,vword (lowRun m g B p a l j).flags e=maskWord (flagBad (lowBad m g p a B) j e) := by
  induction j with
  | zero => intro e he; simp [lowRun,flagBad,maskWord,vword]
  | succ j ih =>
    intro e he
    rw [lowRun]
    simp only [lowStep,laneVector_word _ he]
    rw [ih (by omega) e he,lowOutput_current m g B p a l hpl hap hal (by omega) he,
      lowSigned_mask hg m p a _ (ha _ (by omega)) (hb _ (by omega)) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def lowBody (g : Nat) : List Instr := [0,16,32,48].flatMap (subGroup g)

theorem lowBody_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s : State} {m : Mem} {p a l : Addr} {u : Nat}
    (hr : LowReady g B s) (hm : s.mem=(lowRun m g B p a l (4*u)).mem) (hf : s.v .v31=(lowRun m g B p a l (4*u)).flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=l+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hl : ∀i<4,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (lowBody g)) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t ∧ LowReady g B t ∧
      t.mem=(lowRun m g B p a l (4*(u+1))).mem ∧ t.v .v31=(lowRun m g B p a l (4*(u+1))).flags := by
  let I := fun i t => StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t ∧ LowReady g B t ∧
    t.mem=(lowRun m g B p a l (4*u+i)).mem ∧ t.v .v31=(lowRun m g B p a l (4*u+i)).flags
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (subGroup g (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags⟩
    refine WP.mono (subGroup_step hg hi hready hmem hflags
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ((hk.keep.get .x2).trans h2) ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · simpa only [hk.keep.wr,hk.keep.get .x2] using hl i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_⟩
      · rw [show 4*u+(i+1)=4*u+i+1 by omega,lowRun]
        with_reducible exact hmv
      · rw [show 4*u+(i+1)=4*u+i+1 by omega,lowRun]
        with_reducible exact hfv
  have h := fourGroups_ok (subGroup g) I hinit hstep
  simpa only [I,lowBody,show 4*u+4=4*(u+1) by omega] using h

theorem lowLoop_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s : State} (hr : LowReady g B s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (lowBody g++advance [.x0,.x1,.x2])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x2,.x10] s t ∧ LowReady g B t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧ t.gpr .x2=s.gpr .x2+1024 ∧
      t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.v .v31=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  let I := fun u t => Keep [.x0,.x1,.x2,.x10] s t ∧ LowReady g B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (64*u) ∧
    t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).mem ∧
    t.v .v31=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).flags
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,h2,hm,hf⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (lowBody_ok hg hready hm hf h0 h1 h2 ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
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
      simp only [hk.wr,h2,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hl _ (by omega)
    · refine WP.mono (advance3_ok v) fun w ⟨⟨⟨hw0,hw1,hw2,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,?_,hwm.trans hmv,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by intro r _; exact congrFun hvw r) (by simp)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw2,hv.keep.get .x2,h2,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,by simp,rfl,hf⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowCore.lean` -/

section

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

end
