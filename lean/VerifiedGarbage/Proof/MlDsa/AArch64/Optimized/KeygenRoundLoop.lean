import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep fourGroups_ok advance advance3_ok)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

def fourBody : List Instr := [0,16,32,48].flatMap body

theorem fourBody_ok {s : State} {m : Mem} {input high low : Addr} {u : Nat}
    (hr : Ready s) (hm : s.mem=roundRun m input high low (4*u))
    (h0 : s.gpr .x0=input+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=high+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=low+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hh : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hl : ∀i<4,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block fourBody) s fun t =>
      StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundRun m input high low (4*(u+1)) := by
  let I := fun i t=>StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundRun m input high low (4*u+i)
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (body (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem⟩
    refine WP.mono (body_step hi hready ((hk.keep.get .x0).trans h0)
      ((hk.keep.get .x1).trans h1) ((hk.keep.get .x2).trans h2) ?_ ?_ ?_) fun v ⟨hv,hrv,hmv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.wr,hk.keep.get .x1] using hh i hi
    · simpa only [hk.keep.wr,hk.keep.get .x2] using hl i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_⟩
      change v.mem=roundRun m input high low (4*u+(i+1))
      rw [show 4*u+(i+1)=4*u+i+1 by omega,roundRun_next,←hmem]
      exact hmv
  simpa only [I,fourBody,show 4*u+4=4*(u+1) by omega] using fourGroups_ok body I hinit hstep

theorem roundLoop_ok {s : State} (hr : Ready s) (hc : s.gpr .x10=16)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (fourBody++advance [.x0,.x1,.x2])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x2,.x10] s t ∧ Ready t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧ t.gpr .x2=s.gpr .x2+1024 ∧
      t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64 := by
  let I := fun u t=>Keep [.x0,.x1,.x2,.x10] s t ∧ Ready t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (64*u) ∧
    t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,h2,hm⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (fourBody_ok hready hm h0 h1 h2 ?_ ?_ ?_) fun v ⟨hv,hrv,hmv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,←BitVec.ofNat_add]
      exact ha _ (by omega)
    · intro i hi
      simp only [hk.wr,h1,BitVec.add_assoc,←BitVec.ofNat_add]
      exact hh _ (by omega)
    · intro i hi
      simp only [hk.wr,h2,BitVec.add_assoc,←BitVec.ofNat_add]
      exact hl _ (by omega)
    · refine WP.mono (advance3_ok v) fun w ⟨⟨⟨hw0,hw1,hw2,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,?_,hwm.trans hmv⟩,?_⟩
      · exact ⟨by rw [hvw]; exact hrv.q,by rw [hvw]; exact hrv.bias⟩
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw2,hv.keep.get .x2,h2,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
