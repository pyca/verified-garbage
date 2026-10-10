import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRestoreLoop

/-! ## `PairedLowPassFlags` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem allLow_mem (i : LowIndex) : i∈allLow := by
  simp only [allLow,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨i.1,i.2,rfl⟩

theorem allLow_nodup : allLow.Nodup := by decide +kernel

def lowPassAccept (g : Nat) (work out : Addr) (c : LowConstants) (m : Mem)
    (e k : Nat) (i : LowIndex) : Prop :=
  lowPairAccept g (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*k)) 128 p))
    (out+BitVec.ofNat 64 (16*k)) c m e i

theorem lowPass_flag_zero_iff (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n : Nat} (hn : n≤8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    {e : Nat} (he : e<4) :
    vword (lowPassData g work out aux c d n).flags e=0 ↔
      vword d.flags e=0 ∧ ∀k<n,∀i,lowPassAccept g work out c d.mem e k i := by
  induction n with
  | zero => simp only [lowPassData,Nat.not_lt_zero,false_implies,forall_const,and_true]
  | succ n ih =>
    rw [lowPass_step g work out aux c d (by omega) ho ha]
    have hshift : (⟨out+BitVec.ofNat 64 (16*n),2048⟩ : Region).Disjoint
        ⟨aux+BitVec.ofNat 64 (16*n),2048⟩ := by
      intro a hx hy
      exact hd (a-BitVec.ofNat 64 (16*n)) (by
        simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hx)
        (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hy)
    rw [lowRun_flag_zero_iff _ _ _ _ _ _ _ allLow_nodup hshift he,ih (by omega)]
    have ht : (∀i∈allLow,lowPairAccept g
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) c (lowPassData g work out aux c d n).mem e i) ↔
        ∀i,lowPassAccept g work out c d.mem e n i := by
      have hp (i : LowIndex) := lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega : n<8) i
      have heq (i : LowIndex) : lowPairAccept g
          (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
          (out+BitVec.ofNat 64 (16*n)) c (lowPassData g work out aux c d n).mem e i ↔
          lowPassAccept g work out c d.mem e n i := by
        have h0 := hp i 0 hd
        have h1 := hp i 1 hd
        simp only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at h0 h1
        unfold lowPassAccept lowPairAccept
        rw [lowMask_read_eq _ _ _ _ _ h0,lowMask_read_eq _ _ _ _ _ h1]
      exact ⟨fun h i => (heq i).mp (h i (allLow_mem i)),fun h i _ => (heq i).mpr (h i)⟩
    rw [ht]
    constructor
    · rintro ⟨⟨h0,hprev⟩,hlast⟩
      refine ⟨h0,fun k hk i => ?_⟩
      by_cases hkn : k<n
      · exact hprev k hkn i
      · have heq : k=n := by omega
        subst k
        exact hlast i
    · rintro ⟨h0,hall⟩
      exact ⟨⟨h0,fun k hk => hall k (by omega)⟩,hall n (by omega)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowAcceptHalves` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowPairAccept_halves (g : Nat) (v : Values) (out : Addr) (c : LowConstants)
    (m : Mem) (e : Nat) (i : LowIndex) :
    lowPairAccept g v out c m e i ↔
      ∀h:Fin 2,lowMask g m (lowAddr out i h) (lowHalfValue v i h) c e=0 := by
  constructor
  · intro hp h
    fin_cases h
    · exact hp.1
    · exact hp.2
  · intro hp
    exact ⟨hp 0,hp 1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowConstants` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_mono)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Round

def lowConstants (g : Nat) : List Instr :=
  vc .v11 127 ++ vc .v12 (dMul g) ++ vc .v13 (2^(dShift g-1)) ++
  vc .v14 (if g==261888 then 15 else dMod g) ++ vc .v15 (2*g)

theorem lowConstants_ok (g : Nat) (s : State) : WP isa (.block (lowConstants g)) s fun t =>
    SetupKeep [.v11,.v12,.v13,.v14,.v15] s t ∧
    t.v .v11=HighPack.repeatedWord 127 ∧ t.v .v12=HighPack.repeatedWord (dMul g) ∧
    t.v .v13=HighPack.repeatedWord (2^(dShift g-1)) ∧
    t.v .v14=HighPack.repeatedWord (if g==261888 then 15 else dMod g) ∧
    t.v .v15=HighPack.repeatedWord (2*g) := by
  unfold lowConstants
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v11 127) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v12 (dMul g)) fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v13 (2^(dShift g-1))) fun c hc => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok c .v14 (if g==261888 then 15 else dMod g)) fun d hd => ?_
  refine WP.mono (HighPack.vc_ok d .v15 (2*g)) fun t ht => ?_
  refine ⟨setup_mono ((SetupKeep.ofConst ha.1).trans ((SetupKeep.ofConst hb.1).trans
    ((SetupKeep.ofConst hc.1).trans ((SetupKeep.ofConst hd.1).trans (SetupKeep.ofConst ht.1)))))
    (by decide),?_,?_,?_,?_,ht.2⟩
  · rw [ht.1.vec .v11 (by decide),hd.1.vec .v11 (by decide),hc.1.vec .v11 (by decide),hb.1.vec .v11 (by decide),ha.2]
  · rw [ht.1.vec .v12 (by decide),hd.1.vec .v12 (by decide),hc.1.vec .v12 (by decide),hb.2]
  · rw [ht.1.vec .v13 (by decide),hd.1.vec .v13 (by decide),hc.2]
  · rw [ht.1.vec .v14 (by decide),hd.2]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLoop` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round

theorem ready_lowFrame {g : Nat} {s t : State} (h : LowReady g s)
    (hf : CallFrame finalGprs lowRunRegs s t) : LowReady g t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v11 (by decide)]; exact h.c11
  · rw [hf.vec .v12 (by decide)]; exact h.c12
  · rw [hf.vec .v13 (by decide)]; exact h.c13
  · rw [hf.vec .v14 (by decide)]; exact h.c14

theorem lowConstantsAt_callFrame {s t : State} (hf : CallFrame finalGprs lowRunRegs s t) :
    lowConstantsAt t=lowConstantsAt s := by
  unfold lowConstantsAt
  rw [hf.vec .v15 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem lowLoop_ok {g : Nat} (hg : IsG g) {s : State} {table : Addr}
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : LowReady g s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀i:LowIndex,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16) :
    WP isa (.loop (.block (finalLowCode g++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      CallFrame finalGprs lowRunRegs s t ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.gpr .x15=s.gpr .x15+128 ∧ t.gpr .x16=s.gpr .x16+128 ∧
      dataAt t=lowPassData g (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) 8 := by
  let I := fun u t => CallFrame finalGprs lowRunRegs s t ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x15=s.gpr .x15+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x16=s.gpr .x16+BitVec.ofNat 64 (16*u) ∧
    dataAt t=lowPassData g (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hcount
  · intro u hu t hi _
    rcases hi with ⟨hf,h2,h15,h16,hdata⟩
    have hm := congrArg CheckData.mem hdata
    have fm : Frame [⟨s.gpr .x15,2048⟩,⟨s.gpr .x16,2048⟩] s.mem t.mem := by
      change Frame _ _ (dataAt t).mem
      rw [hdata]; exact lowPass_frame _ _ _ _ _ _ (by omega)
    have ht' := tableWords_frame ht fm (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact hd; have he := List.mem_singleton.mp hr; subst r; exact hda)
    have rt : ∀off,off+16≤4096 → InRegions (t.rd++t.wr) (table+BitVec.ofNat 64 off) 16 := by
      simpa only [hf.rd,hf.wr] using hrt
    have hx' : t.gpr .x1=table+BitVec.ofNat 64 3840 := by rw [hf.gpr .x1 (by decide),hx]
    refine finalLow_ok hg ?_ (final_tableReady ht' rt hx') (scale_tableReady ht' rt hx')
      (ready_lowFrame hc hf) ?_ fun a ha had => ?_
    · simpa only [hf.rd,hf.wr,h2] using hr u hu
    · simpa only [hf.rd,hf.wr,h15,h16] using hw u hu
    · refine WP.mono (finalAdvance_ok a) fun b ⟨⟨⟨hb2,hb15,hb16,hb12,hbm⟩,hbk⟩,hbv⟩ => ?_
      have hab := (CallFrame.ofStep ha).trans (CallFrame.ofKeep hbk hbv)
      have hsb : CallFrame finalGprs lowRunRegs s b := (hf.trans hab).mono (by simp [finalGprs]) (by simp)
      refine ⟨⟨hsb,?_,?_,?_,?_⟩,?_⟩
      · rw [hb2,ha.gpr,h2,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb15,ha.gpr,h15,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb16,ha.gpr,h16,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · have hba : dataAt b=dataAt a := by unfold dataAt; rw [hbm,hbv]
        rw [hba,had]
        unfold finalLowData rawPairAt
        rw [h2,h15,h16,lowConstantsAt_callFrame hf,hdata]
        simp only [lowPassData]
        exact congrArg (fun mm => lowRun g (fun p => Inverse.rawFinalValues (readPair mm
          (s.gpr .x2+BitVec.ofNat 64 (16*u)) 128 p)) _ _ _ _ allLow) hm
      · rw [hb12,ha.gpr]; rfl
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReturn` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def lowKernel (g : Nat) : Prog isa :=
  .seq (.loop (.block (finalLowCode g++finalAdvance)) (.nonzero .x .x12))
    (.block (finish .r0))

/-- Exact final inverse/check traversal followed by return and ABI restore. -/
theorem lowKernel_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s₀ s : State} {table work : Addr}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem work s₀.v)
    (hwork : s.gpr .x2=work)
    (hsd : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hrs : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr)
      ((work+BitVec.ofNat 64 128)+BitVec.ofNat 64 p.2) 16)
    (hsda : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : LowReady g s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀i:LowIndex,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16) :
    WP isa (lowKernel g) s fun t =>
      let d := lowPassData g work (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) 8
      Keep ((gr++finalGprs)++([.x0,.x9,.x10] : List Reg)) s₀ t ∧
      t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  unfold lowKernel
  refine loop_finish_ok _ hf hs (vs := lowRunRegs) (writes := [⟨s.gpr .x15,2048⟩,⟨s.gpr .x16,2048⟩])
    (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact hsd;
        have he := List.mem_singleton.mp hr; subst r; exact hsda) hrs ?_
  refine WP.mono (lowLoop_ok hg ht hd hda hx hcount hc hrt hr hw)
    fun t ⟨hft,h2,_,_,hdata⟩ => ?_
  refine ⟨hft,by simpa only [hwork,show (128:Addr)=BitVec.ofNat 64 128 by rfl] using h2,by simpa only [hwork] using hdata,?_⟩
  change Frame _ _ (dataAt t).mem
  rw [hdata]
  exact lowPass_frame _ _ _ _ _ _ (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
