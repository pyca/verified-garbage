import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def addBody : List Instr := [0,16,32,48].flatMap addGroup

theorem addBody_ok {s : State} {m : Mem} {p a : Addr} {B : BitVec 32} {u : Nat}
    (hr : ZReady B s) (hm : s.mem=(zRun m p a B (4*u)).mem) (hf : s.v .v31=(zRun m p a B (4*u)).flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block addBody) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
      t.mem=(zRun m p a B (4*(u+1))).mem ∧ t.v .v31=(zRun m p a B (4*(u+1))).flags := by
  let I := fun i t => StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
    t.mem=(zRun m p a B (4*u+i)).mem ∧ t.v .v31=(zRun m p a B (4*u+i)).flags
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (addGroup (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags⟩
    refine WP.mono (addGroup_step hi hready hmem hflags
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_⟩
      · change v.mem=(zRun m p a B (4*u+(i+1))).mem
        rw [show 4*u+(i+1)=4*u+i+1 by omega,zRun_next]
        exact hmv
      · change v.v .v31=(zRun m p a B (4*u+(i+1))).flags
        rw [show 4*u+(i+1)=4*u+i+1 by omega,zRun_next]
        exact hfv
  have h := fourGroups_ok addGroup I hinit hstep
  simpa only [I,addBody,show 4*u+4=4*(u+1) by omega] using h

theorem addLoop_ok {s : State} (hr : ZReady ((s.gpr .x2).setWidth 32) s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x10] s t ∧ ZReady ((s.gpr .x2).setWidth 32) t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  let B := (s.gpr .x2).setWidth 32
  let I := fun u t => Keep [.x0,.x1,.x10] s t ∧ ZReady B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).mem ∧
    t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).flags
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,hm,hf⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (addBody_ok hready hm hf h0 h1 ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact ha _ (by omega)
    · intro i hi
      simp only [hk.rd,hk.wr,h1,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hb _ (by omega)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega)
    · refine WP.mono (advance2_ok v) fun w ⟨⟨⟨hw0,hw1,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,hwm.trans hmv,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by simp) (by intro r _; exact congrFun hvw r)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,rfl,hf⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response
