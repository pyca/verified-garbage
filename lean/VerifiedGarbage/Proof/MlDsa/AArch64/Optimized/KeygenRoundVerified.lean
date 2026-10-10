import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundSemantic

/-! ## From `KeygenRoundLoop.lean` -/

section

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

end

/-! ## From `KeygenRoundCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord_lane)

theorem setup_ok (s : State) :
    WP isa (.block (vc .v16 8380417 ++ vc .v17 4095)) s fun t =>
      SetupKeep [.v16,.v17] s t ∧ Ready t := by
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ha => ?_
  refine WP.mono (HighPack.vc_ok a .v17 4095) fun t ht => ?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem run_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa power2Round s fun t =>
      t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64 := by
  unfold power2Round loop
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨hk,hr⟩ => ?_)
  refine WP.seq (WP.mono (Response.counter_ok a) fun b ⟨⟨hc,hm⟩,hv⟩ => ?_)
  have hb : Ready b := ⟨by rw [hv]; exact hr.q,by rw [hv]; exact hr.bias⟩
  have h0 : b.gpr .x0=s.gpr .x0 := (hm.get .x0).trans (hk.gpr .x0 (by decide))
  have h1 : b.gpr .x1=s.gpr .x1 := (hm.get .x1).trans (hk.gpr .x1 (by decide))
  have h2 : b.gpr .x2=s.gpr .x2 := (hm.get .x2).trans (hk.gpr .x2 (by decide))
  refine WP.mono (roundLoop_ok hb hc.1 ?_ ?_ ?_) fun t ht => ?_
  · simpa only [hm.rd,hm.wr,hk.rd,hk.wr,h0] using ha
  · simpa only [hm.wr,hk.wr,h1] using hh
  · simpa only [hm.wr,hk.wr,h2] using hl
  · simpa only [h0,h1,h2,hc.2,hk.mem] using ht.2.2.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

/-! ## From `KeygenRoundVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Round (power2RoundK p2rSat)
open VG.Proof.MlDsa.Round (natPolyIs_of_toNat map_get)
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem correct (s : State) (hp : power2RoundK.pre s) :
    ∃tr t, Exec isa VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round s tr t ∧
      abiPreserved s t ∧ power2RoundK.post s t := by
  obtain ⟨tr,t,he,hm⟩ := run_ok s (fun off ho =>
    ⟨pR (s.gpr .x0),by rw [hp.1]; simp,Offset.contains_base _ ho (by omega)⟩)
    (fun off ho => ⟨pR (s.gpr .x1),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega)⟩)
    (fun off ho => ⟨pR (s.gpr .x2),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega)⟩)
  have hfield := roundRun_prefix s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 (by decide : 64≤64)
  have hr := hp.2.2.2.2.2
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,?_,?_⟩
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).1,ite_eq_left (by omega),highWord_eq (hr k hk),map_get _ _ hk,
      Round.t1V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_eq,←polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).2,ite_eq_left (by omega),lowWord_eq (hr k hk),map_get _ _ hk,
      Round.t0V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_t0,polyAt_val hr hk]

theorem constantTime : ConstantTime isa power2RoundK.pre power2RoundK.pub
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2.2 fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      exacts [hp.1,hp.2.1,hp.2.2.1]) (by taint_decide)

theorem power2Round_verified : Verified target
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round (power2RoundContract abi) :=
  Verified.of_correct correct constantTime (by
    mldsa_implies [power2RoundContract,power2RoundSig,power2RoundK,abi,argRegs] [p2rSat] using p2rSat)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end
