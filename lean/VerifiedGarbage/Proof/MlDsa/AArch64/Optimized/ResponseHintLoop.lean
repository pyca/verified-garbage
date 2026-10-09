import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop

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
