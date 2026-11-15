module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourReady
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeApart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFlags
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitialized
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi

/-! ### `MlDsa.AArch64.Optimized.BoundedFourRound`, which only this module used -/

section

/-! ## From `BoundedFourSqueezeReady.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLayout_covers (c : SqueezeCfg) {j : Nat} (hj : j<2) :
    ∀r∈c.stepWrites j,∃t∈c.writes,Region.Sub r t := by
  intro r hr
  simp only [SqueezeCfg.stepWrites,pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  have hout (i : Nat) : Region.Sub (rateR (c.at i j)) ⟨c.out i,272⟩ :=
    Offset.sub_base _ (by omega_arith)
  rcases hr with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|rfl
  · exact ⟨pairR c.p,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 0,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 0⟩
  · exact ⟨⟨c.out 1,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 1⟩
  · exact ⟨pairR c.q,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 2,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 2⟩
  · exact ⟨⟨c.out 3,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 3⟩
  · exact ⟨X2.callR c.w,by simp [SqueezeCfg.writes],fun _ h=>h⟩

theorem squeezeLayout_call {s : State} {b : Addr} {off d : Nat} (hd : d+400≤3024)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    Covers [pairR (b+BitVec.ofNat 64 d),X2.callR (squeezeCfg b off).w] s.wr := by
  refine Covers.of_forall fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact Covers.one (hw d 400 (by omega_arith))
  · exact Covers.one (hw 3024 136 (by decide))

theorem squeezeLayout_ok {s : State} {b : Addr} {off : Nat} (ho : off≤272) (hb : s.gpr .x19=b)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    SqueezeLayout s (squeezeCfg b off) :=
  ⟨fun _ hj=>squeezeLayout_left ho hj hw,fun _ hj=>squeezeLayout_right ho hj hw,
    fun _ hj=>squeezeLayout_apart b ho hj,
    fun _ hi _ _ hkj hj=>squeezeLayout_past b ho hi hkj hj,
    fun _ hj=>squeezeLayout_covers _ hj,by rw [hb]; rfl,
    fun _ hj=>squeezeLayout_scratch b ho hj,
    by have h := squeezeLayout_call (off := off) (d := 0) (by decide) hw
       rwa [BitVec.add_zero] at h,
    squeezeLayout_call (off := off) (d := 400) (by decide) hw⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatchLayout.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

theorem sampler_work_read {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions (s.rd++s.wr) (samplerAt σ d) n := by
  obtain ⟨r,hr,hc⟩:=sampler_in_work hp hw hd
  exact ⟨r,List.mem_append_right _ hr,hc⟩

theorem inputAt_sub (b : Addr) {i off : Nat} (hi : i<4) (ho : off≤272) :
    Region.Sub (⟨inputAt b i off,274⟩ : Region) ⟨b,8192⟩ :=
  Offset.sub_base b (d := 840+544*i+off) (n := 274) (k := 8192) (by omega_arith)

theorem samplerBatchLayout_ok {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {off : Nat} (ho : off≤272) {X : Nat→List Byte}
    (hlen : ∀i<4,(X i).length=272)
    (hbytes : ∀i<4,∀j<272,s.mem (inputAt (samplerScratch σ) i off+BitVec.ofNat 64 j)=(X i)[j]!) :
    BatchLayout s (samplerScratch σ) (samplerOut σ) off X := by
  let b:=samplerScratch σ
  let p:=samplerOut σ
  have hstream (i : Nat) (hi : i<4) :
      (⟨inputAt b i off,(X i).length+2⟩ : Region).Disjoint (polyR (outputAt p i)) := by
    rw [hlen i hi]
    exact (hp.output_work.symm.sub_left (inputAt_sub _ hi ho)).sub_right (outputAt_sub _ hi)
  have htable (i : Nat) (hi : i<4) :
      (⟨b+6000,1024⟩ : Region).Disjoint (polyR (outputAt p i)) :=
    (hp.output_work.symm.sub_left (Offset.sub_base b (d := 6000) (n := 1024) (k := 8192)
      (by decide))).sub_right (outputAt_sub _ hi)
  have hout (i : Nat) (hi : i<4) (j n : Nat) (hj : 4*j+n≤1024) :
      InRegions s.wr (coeffAddr (outputAt p i) j) n := by
    rw [hw,hp.wr]
    refine ⟨samplerOutput σ,by simp,?_⟩
    change Region.Contains ⟨p,4096⟩ ((p+BitVec.ofNat 64 (1024*i))+BitVec.ofNat 64 (4*j)) n
    rw [Offset.add_add]
    exact Offset.contains_base p (by omega_arith) (by omega_arith)
  constructor
  · exact hlen
  · intro i hi
    refine ⟨by rw [hlen i hi],by rw [hlen i hi],?_,hstream i hi,htable i hi,?_,?_,?_⟩
    · intro j hj; exact hbytes i hi j (by simpa only [hlen i hi] using hj)
    · intro d hd
      rw [hlen i hi] at hd
      change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 (840+544*i+off))+BitVec.ofNat 64 d) 4
      rw [Offset.add_add]
      exact sampler_work_read hp hw (by omega_arith)
    · intro m hm
      constructor
      · change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*m)) 16
        rw [Offset.add_add]
        exact sampler_work_read hp hw (by omega_arith)
      · change InRegions (s.rd++s.wr) (((b+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*m))+BitVec.ofNat 64 32) 8
        rw [Offset.add_add,Offset.add_add]
        exact sampler_work_read hp hw (by omega_arith)
    · intro j hj; exact hout i hi j 16 (by omega_arith)
  · intro i hi
    refine ⟨by rw [hlen i hi],?_,?_,?_,?_⟩
    · intro j hj; exact hbytes i hi j (by simpa only [hlen i hi] using hj)
    · exact (hstream i hi).sub_left (Region.sub_prefix (by omega_arith))
    · intro d hd
      rw [hlen i hi] at hd
      change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 (840+544*i+off))+BitVec.ofNat 64 d) 1
      rw [Offset.add_add]
      exact sampler_work_read hp hw (by omega_arith)
    · intro j hj; exact hout i hi j 4 (by omega_arith)
  · intro i hi r hr
    rw [hlen i hi]
    rcases (show r=⟨p,4096⟩∨r=⟨b+7904#64,32⟩ by simpa [batchWrites] using hr) with rfl|rfl
    · exact hp.output_work.symm.sub_left (inputAt_sub _ hi ho)
    · exact Offset.disjoint b (d := 840+544*i+off) (e := 7904) (n := 274) (k := 32)
        (by omega_arith) (by omega_arith) (by decide)
  · intro r hr
    rcases (show r=⟨p,4096⟩∨r=⟨b+7904#64,32⟩ by simpa [batchWrites] using hr) with rfl|rfl
    · exact hp.output_work.symm.sub_left (Offset.sub_base b (d := 6000) (n := 1024) (k := 8192) (by decide))
    · exact Offset.disjoint b (d := 6000) (e := 7904) (n := 1024) (k := 32) (by decide) (by decide) (by decide)
  · intro i hi j hj
    exact (hp.output_work.sub_left (outputAt_sub _ hi)).sub_right
      (Offset.sub_base b (d := 7904+8*j) (n := 8) (k := 8192) (by omega_arith))
  · intro i hi; exact sampler_work_read hp hw (by omega_arith)
  · intro i hi; exact sampler_in_work hp hw (by omega_arith)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeTwo.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeAllRegs : List Reg := squeezeRegs++[.x22,.x23]

structure SqueezePost (s t : State) (b : Addr) (off : Nat) (A : Nat→Spec.Sha3.State) : Prop where
 keep : RegKeep squeezeAllRegs s t
 frame : Frame (squeezeCfg b off).writes s.mem t.mem
 first : PairAt t.mem b (Resident.permuted (A 0) 2) (Resident.permuted (A 1) 2)
 second : PairAt t.mem (b+400#64) (Resident.permuted (A 2) 2) (Resident.permuted (A 3) 2)
 streams : ∀i<4,Stream136 t.mem ((squeezeCfg b off).out i) 2 (A i)

theorem squeezeTwo_ok (sha3 : Bool) {s : State} {b : Addr} {off : Nat} {A : Nat→Spec.Sha3.State}
    (ho : off≤272) (hb : s.gpr .x19=b)
    (hP : PairAt s.mem b (A 0) (A 1)) (hQ : PairAt s.mem (b+400#64) (A 2) (A 3))
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off) s fun t=>
      SqueezePost s t b off A := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo
  refine WP.seq (WP.mono (squeezeArgs_ok s ho) fun u ⟨⟨⟨h22,h23,h24,h25,h26,h27,h28,hm⟩,hk⟩,_⟩=>?_)
  rw [hb] at h22 h23 h24 h25 h26 h27
  have hi : SqueezeInv u u (squeezeCfg b off) A 0 := by
    refine ⟨by decide,RegKeep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hm]; exact hP
    · rw [hm]; exact hQ
    · intro i hi; exact stream136_zero _ _ _
    · exact h22
    · exact h23
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h24
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h25
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h26
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h27
    · exact h28
  have hl : SqueezeLayout u (squeezeCfg b off) := squeezeLayout_ok ho
    (by rw [hk.gpr .x19 (by decide),hb]) (fun o n hn=>by
    rw [hk.wr]; exact hw o n hn)
  refine WP.mono (squeezeLoop_ok sha3 hl hi (by decide)) fun t ht=>?_
  have hr : RegKeep [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s u := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  refine ⟨(hr.trans ht.keep).mono (by decide),?_,ht.first,ht.second,ht.streams⟩
  rw [←hm]; exact ht.frame

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourRunState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.Sha3.AArch64.Neon

structure SamplerRun (σ s : State) (A : Nat→Spec.Sha3.State) (L : Nat→List Zq) : Prop where
 env : SamplerEnv σ s
 pair0 : PairAt s.mem (samplerScratch σ) (A 0) (A 1)
 pair1 : PairAt s.mem (samplerScratch σ+400#64) (A 2) (A 3)
 table : TableAt s.mem (samplerScratch σ+6000)
 fields : BatchFields s.mem (samplerScratch σ) (samplerOut σ) L

theorem Ready.running {σ s : State} (h : Ready σ s) : SamplerRun σ s (samplerA σ) (fun _=>[]) := by
  refine ⟨h.env,?_,?_,h.table,⟨by simp,by intro i hi j hj; simp at hj,?_⟩⟩
  · have hh:=h.pair 0 (by decide)
    change PairAt s.mem (samplerScratch σ+0#64) (samplerA σ 0) (samplerA σ 1) at hh
    rw [BitVec.add_zero] at hh
    exact hh
  · exact h.pair 1 (by decide)
  · intro i hi; exact h.counts i hi

theorem squeezeWrites_sub {b : Addr} {off : Nat} (ho : off≤272) {r : Region}
    (hr : r∈(squeezeCfg b off).writes) : Region.Sub r ⟨b,4096⟩ := by
  simp only [SqueezeCfg.writes,squeezeCfg,pairR,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Region.sub_prefix (by decide)
  · exact Offset.sub_base b (d := 400) (n := 400) (k := 4096) (by decide)
  · exact Offset.sub_base b (d := 840+off) (n := 272) (k := 4096) (by omega_arith)
  · exact Offset.sub_base b (d := 1384+off) (n := 272) (k := 4096) (by omega_arith)
  · exact Offset.sub_base b (d := 1928+off) (n := 272) (k := 4096) (by omega_arith)
  · exact Offset.sub_base b (d := 2472+off) (n := 272) (k := 4096) (by omega_arith)
  · exact Offset.sub_base b (d := 3024) (n := 136) (k := 4096) (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeStage.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeStage_ok (sha3 : Bool) {σ s : State} (hp : SamplerPre σ)
    {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off) s fun t=>
      SamplerRun σ t (fun i=>Resident.permuted (A i) 2) L ∧
      (∀i<4,Stream136 t.mem (inputAt (samplerScratch σ) i off) 2 (A i)) := by
  refine WP.mono (squeezeTwo_ok sha3 ho hs.env.x19 hs.pair0 hs.pair1
    (fun o n h=>sampler_in_work hp hs.env.wr h)) fun t ht=>?_
  have hlow : ∀r∈(squeezeCfg (samplerScratch σ) off).writes,
      Region.Sub r ⟨samplerScratch σ,4096⟩ := fun _ hr=>squeezeWrites_sub ho hr
  have ho' : (samplerOutput σ).Disjoint (⟨samplerScratch σ,4096⟩ : Region) :=
    hp.output_work.sub_right (Region.sub_prefix (by decide))
  have htable : (⟨samplerScratch σ+6000,1024⟩ : Region).Disjoint ⟨samplerScratch σ,4096⟩ := by
    have hh := (Offset.disjoint (samplerScratch σ)
      (d := 6000) (e := 0) (n := 1024) (k := 4096) (by decide) (by decide) (by decide))
    simp only [BitVec.add_zero] at hh
    exact hh
  refine ⟨⟨?_,ht.first,ht.second,hs.table.frame ht.frame (fun r hr=>htable.sub_right (hlow r hr)),?_,⟩,?_⟩
  · exact hs.env.lowStep ht.frame (fun r hr=>fun x hx=>
      (Region.sub_prefix (by decide : 4096≤7968)) x (hlow r hr x hx))
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.gpr r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · refine ⟨hs.fields.bound,?_,?_⟩
    · intro i hi
      exact stored_frame ht.frame (fun r hr=>(ho'.sub_left (outputAt_sub _ hi)).sub_right (hlow r hr))
        (hs.fields.stored i hi) (hs.fields.bound i hi)
    · intro i hi
      have hc : (⟨countAt (samplerScratch σ) i,8⟩ : Region).Disjoint ⟨samplerScratch σ,4096⟩ := by
        have hh := (Offset.disjoint (samplerScratch σ)
          (d := 7904+8*i) (e := 0) (n := 8) (k := 4096) (by omega_arith) (by omega_arith) (by decide))
        simp only [BitVec.add_zero] at hh
        exact hh
      rw [ht.frame.readW (Region.contains_self _ _) (fun r hr=>hc.sub_right (hlow r hr)) (by decide)]
      exact hs.fields.count i hi
  · intro i hi
    simpa only [squeezeCfg_out _ _ hi,inputAt] using ht.streams i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatchStage.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem batchStage_ok {η : Nat} (hη : η=2∨η=4) {σ s : State} (hp : SamplerPre σ)
    {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) {X : Nat→List Byte}
    (hl : BatchLayout s (samplerScratch σ) (samplerOut σ) off X) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off) s fun t=>
      SamplerRun σ t A (fun i=>rbFold η (L i) (X i)) := by
  have hi : BatchInv s s (samplerScratch σ) (samplerOut σ) L :=
    ⟨Keep.refl _ _,Frame.refl _ _,hs.env.x19,hs.env.x21,hs.table,hs.fields⟩
  refine WP.mono (batch_ok hη ho hl hi) fun t ht=>?_
  have hcount : (⟨samplerScratch σ+7904#64,32⟩ : Region).Sub (samplerWorkspace σ) :=
    Offset.sub_base _ (d := 7904) (n := 32) (k := 8192) (by decide)
  have hout : (ResidentRej.saveR σ).Disjoint (samplerOutput σ) :=
    (hp.output_work.sub_right (Offset.sub_base _ (d := 7968) (n := 144) (k := 8192) (by decide))).symm
  have hsave : (ResidentRej.saveR σ).Disjoint (⟨samplerScratch σ+7904#64,32⟩ : Region) :=
    Offset.disjoint _ (d := 7968) (e := 7904) (n := 144) (k := 32) (by decide) (by decide) (by decide)
  have hpair (p : Nat) (hpn : p<2) :
      (pairR (ResidentRej.stateP σ p)).Disjoint (samplerOutput σ) :=
    (hp.output_work.sub_right (Offset.sub_base _ (d := 400*p) (n := 400) (k := 8192) (by omega_arith))).symm
  have pairKeep (p : Nat) (hpn : p<2) (a b : Spec.Sha3.State)
      (hh : PairAt s.mem (ResidentRej.stateP σ p) a b) :
      PairAt t.mem (ResidentRej.stateP σ p) a b := by
    intro i hii
    rw [ht.frame.read (pair_contains _ hii) (fun r hr=>by
      rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
      · exact hpair p hpn
      · exact Offset.disjoint _ (d := 400*p) (e := 7904) (n := 400) (k := 32) (by omega_arith) (by omega_arith) (by decide)) (by decide)]
    exact hh i hii
  refine ⟨?_,?_,?_,ht.table,ht.fields⟩
  · exact hs.env.frameStep ht.frame (fun r hr=>by
      rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
      · exact ⟨ResidentRej.aR 4 σ,by simp,fun _ h=>h⟩
      · exact ⟨ResidentRej.scrR σ,by simp,hcount⟩)
      (fun r hr=>by
        rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
        · exact hout
        · exact hsave)
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · have he : ResidentRej.stateP σ 0=samplerScratch σ := by change samplerScratch σ+0#64=_; exact BitVec.add_zero _
    have h0:=hs.pair0
    rw [←he] at h0 ⊢
    exact pairKeep 0 (by decide) _ _ h0
  · exact pairKeep 1 (by decide) _ _ hs.pair1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourRound.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def chunkBytes (A : Spec.Sha3.State) : List Byte :=
 List.ofFn fun i : Fin 272=>Proof.Sha3.byteOf (Resident.permuted A (i.val/136+1)) (i.val%136)

theorem chunkBytes_length (A : Spec.Sha3.State) : (chunkBytes A).length=272 := List.length_ofFn

theorem chunkBytes_get (A : Spec.Sha3.State) {i : Nat} (hi : i<272) :
    (chunkBytes A)[i]! =Proof.Sha3.byteOf (Resident.permuted A (i/136+1)) (i%136) := by
  simp only [chunkBytes,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]

theorem sampleRound_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ s : State}
    (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off)) s fun t=>
      SamplerRun σ t (fun i=>Resident.permuted (A i) 2) (fun i=>rbFold η (L i) (chunkBytes (A i))) := by
  refine WP.seq (WP.mono (squeezeStage_ok sha3 hp hs ho) fun t ⟨ht,hstreams⟩=>?_)
  have hl : BatchLayout t (samplerScratch σ) (samplerOut σ) off (fun i=>chunkBytes (A i)) :=
    samplerBatchLayout_ok hp ht.env.wr ho (fun _ _=>chunkBytes_length _) (fun i hi j hj=>by
      rw [chunkBytes_get _ hj]
      exact stream136_byte (hstreams i hi) (by omega_arith))
  exact batchStage_ok hη hp ht ho hl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourCore.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourAdaptive.lean`, which only this module imported.
section

/-! ## From `BoundedFourRunFlags.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

theorem SamplerRun.only {σ s t : State} {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (h : SamplerRun σ s A L) {rs : List Reg} (ht : Only rs s t)
    (hr : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : SamplerRun σ t A L := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r h=>ht.get r (hr r h)),?_,?_,?_,?_⟩ <;>
    rw [ht.mem]
  · exact h.pair0
  · exact h.pair1
  · exact h.table
  · exact h.fields

def countFlag (L : Nat→List Zq) : BitVec 64 := foldedFlags (fun i=>BitVec.ofNat 64 (256-(L i).length)) 3

theorem countFlag_zero {L : Nat→List Zq} (h : ∀i<4,(L i).length≤256) :
    countFlag L=0#64 ↔∀i<4,(L i).length=256 := by
  rw [countFlag,ResidentRej.foldedFlags_zero]
  constructor
  · intro hz i hi
    have hh:=congrArg BitVec.toNat (hz i hi)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])] at hh
    change 256-(L i).length=0 at hh
    have:=h i hi
    omega_using [hh, this]
  · intro hz i hi
    rw [hz i hi]

theorem flagsStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) s fun t=>
      SamplerRun σ t A L ∧t.gpr .x27=countFlag L := by
  refine WP.mono (flags_ok hs.env.x19 hs.fields.count
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega_using [hi]))) fun t ⟨⟨ht,hflag⟩,_⟩=>?_
  exact ⟨hs.only ht (by decide),hflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAdaptive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem SamplerRun.congr {σ s : State} {A : Nat→Spec.Sha3.State} {L K : Nat→List Zq}
    (h : SamplerRun σ s A L) (he : ∀i<4,L i=K i) : SamplerRun σ s A K := by
  refine ⟨h.env,h.pair0,h.pair1,h.table,⟨?_,?_,?_⟩⟩
  · intro i hi; rw [←he i hi]; exact h.fields.bound i hi
  · intro i hi; rw [←he i hi]; exact h.fields.stored i hi
  · intro i hi; rw [←he i hi]; exact h.fields.count i hi

theorem countFlag_congr {L K : Nat→List Zq} (he : ∀i<4,L i=K i) : countFlag L=countFlag K := by
  unfold countFlag foldedFlags
  change ((BitVec.ofNat 64 (256-(L 0).length)|||BitVec.ofNat 64 (256-(L 1).length))|||
    BitVec.ofNat 64 (256-(L 2).length))|||BitVec.ofNat 64 (256-(L 3).length)=_
  rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]
  rfl

def secondBatch (sha3 : Bool) (η : Nat) : Prog isa :=
 .ite (.zero .x .x27) (.block [])
  (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 272)
   (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η 272)
    (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags)))

theorem secondBatch_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ s : State}
    (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (hs : SamplerRun σ s A L) (hflag : s.gpr .x27=countFlag L) :
    WP isa (secondBatch sha3 η) s fun t=>
      ∃A',SamplerRun σ t A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        t.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) := by
  unfold secondBatch
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _=>?_) (by simp)
    have hfull := (countFlag_zero hs.fields.bound).mp (hflag.symm.trans hz)
    have he : ∀i<4,L i=rbFold η (L i) (chunkBytes (A i)) := fun i hi=>
      (rbFold_full (hfull i hi) _).symm
    exact WP.block_nil_iff.mpr ⟨A,hs.congr he,hflag.trans (countFlag_congr he)⟩
  · refine WP.ite false (by rw [eval_zero,show (s.gpr .x27 == 0)=false from beq_eq_false_iff_ne.mpr hz])
      (by simp) (fun _=>?_)
    have hc:=WP.seq (WP.mono (sampleRound_ok sha3 hη hp hs (by decide : 272≤272)) fun t ht=>
      WP.mono (flagsStage_ok hp ht) fun u ⟨hu,hf⟩=>
        (show ∃A',SamplerRun σ u A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
          u.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) from ⟨_,hu,hf⟩))
    simpa only [WP.seq_iff (M := isa)] using hc

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourFinish.lean`, which only this module imported.
section

/-! ## From `BoundedFourMasked.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def resultWord (L : List Zq) (j : Nat) : BitVec 32 := if L.length=256 then zw (L.getD j 0) else 0#32

structure Sampled (σ s : State) (L : Nat→List Zq) : Prop where
 env : SamplerEnv σ s
 bound : ∀i<4,(L i).length≤256
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 flag : s.gpr .x27=countFlag L

theorem maskStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) (hf : s.gpr .x27=countFlag L) :
    WP isa maskFour s (fun t=>Sampled σ t L) := by
  have hout (i j : Nat) (hi : i<4) (hj : j<64) :
      InRegions s.wr (outputAt (samplerOut σ) i+BitVec.ofNat 64 (16*j)) 16 := by
    rw [hs.env.wr,hp.wr]
    refine ⟨samplerOutput σ,by simp,?_⟩
    unfold outputAt
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_using [hi, hj]) (by omega_using [hi, hj])
  refine WP.mono (maskFour_ok hs.env.x19 hs.env.x21
    (fun i hi=>by rw [hs.fields.count i hi,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])]; omega_using [])
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega_using [hi]))
    (fun i hi j hj=>by obtain ⟨r,hr,hc⟩:=hout i j hi hj; exact ⟨r,List.mem_append_right _ hr,hc⟩)
    (fun i hi j hj=>hout i j hi hj)
    (fun i hi j hj=>(hp.output_work.symm.sub_left
      (Offset.sub_base _ (d := 7904+8*i) (n := 8) (k := 8192) (by omega_using [hi]))).sub_right (outputAt_sub _ hj)))
    fun t ht=>?_
  refine ⟨?_,hs.fields.bound,?_,(ht.keep.get .x27).trans hf⟩
  · exact hs.env.frameStep ht.frame (fun r hr=>by
      rw [List.mem_singleton.mp hr]
      exact ⟨ResidentRej.aR 4 σ,by simp,fun _ h=>h⟩)
      (fun r hr=>by rw [List.mem_singleton.mp hr]; exact
        (hp.output_work.sub_right (Offset.sub_base _ (d := 7968) (n := 144) (k := 8192) (by decide))).symm)
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · intro i hi j hj
    rw [ht.words i hi j hj,ite_eq_left hi]
    unfold maskedWord resultWord
    rw [hs.fields.count i hi]
    by_cases hfull : (L i).length=256
    · rw [hfull,ite_eq_left rfl,ite_eq_left rfl]
      exact hs.fields.stored i hi j (by omega_using [hj, hfull])
    · have hn : BitVec.ofNat 64 (256-(L i).length)≠0#64 := by
        intro he
        have hh:=congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])] at hh
        change 256-(L i).length=0 at hh
        have:=hs.fields.bound i hi
        omega_using [hfull, hh, this]
      rw [ite_eq_right hn,ite_eq_right hfull]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

local instance (L : Nat→List Zq) : Decidable (∀i<4,(L i).length=256) :=
 Nat.decidableBallLT 4 (fun i _=>(L i).length=256)

structure Result (σ t : State) (L : Nat→List Zq) : Prop where
 abi : abiPreserved σ t
 frame : Frame [samplerOutput σ,samplerWorkspace σ] σ.mem t.mem
 rd : t.rd=σ.rd
 wr : t.wr=σ.wr
 words : ∀i<4,∀j<256,coeffAt t.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 status : t.gpr .x0=if (∀i<4,(L i).length=256) then 1#64 else 0#64

theorem finish_ok {σ s : State} (hp : SamplerPre σ) {L : Nat→List Zq} (h : Sampled σ s L) :
    WP isa (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) s (fun t=>Result σ t L) := by
  refine wp_subImm (by decide) fun a ha ea=>wp_lsr (by decide) fun b hb eb=>?_
  have he : SamplerEnv σ b := h.env.lowStep (rs := [])
    (by rw [hb.mem,ha.mem]; exact Frame.refl _ _) (by simp)
    (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.sp.trans ha.sp)
    (fun r hr=>by
      have hn : r∉[Reg.x27] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      rw [hb.get r hn,ha.get r hn])
  have hbound : (countFlag L).toNat<512 := ResidentRej.foldedFlags_bound _ _ (fun i hi=>by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [])
  have eflag : b.gpr .x27=if (∀i<4,(L i).length=256) then 1#64 else 0#64 := by
    rw [eb,ea,h.flag,ResidentRej.smallFlag_status _ hbound]
    by_cases hz : countFlag L=0#64
    · rw [ite_eq_left hz,ite_eq_left ((countFlag_zero h.bound).mp hz)]
    · rw [ite_eq_right hz,ite_eq_right (fun hh=>hz ((countFlag_zero h.bound).mpr hh))]
  refine WP.mono (ResidentRej.epi_with he (fun d n hn=>sampler_work_read hp he.wr hn)) fun t ht=>?_
  exact ⟨ht.1,by rw [ht.2.1]; exact he.frame,ht.2.2.2.1.trans he.rd,
    ht.2.2.2.2.trans he.wr,by simpa only [ht.2.1,hb.mem,ha.mem] using h.words,
    ht.2.2.1.trans eflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def sampledRows (σ : State) (η : Nat) (i : Nat) : List Zq :=
 rbFold η (rbFold η [] (chunkBytes (samplerA σ i)))
  (chunkBytes (Resident.permuted (samplerA σ i) 2))

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State→Prop} :
    WP isa (.seq a (.seq b c)) s Q↔WP isa (.seq (.seq a b) c) s Q := by
  simp only [WP.seq_iff (M := isa)]

theorem sampler_machine_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ : State}
    (hp : SamplerPre σ) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) σ
      (fun t=>Result σ t (sampledRows σ η)) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change WP isa (.seq (.block samplerSetup) _) σ _
  refine WP.seq (WP.mono (samplerSetup_ok hp) fun a ha=>?_)
  rw [wp_seq_assoc]
  refine WP.seq (WP.mono (sampleRound_ok sha3 hη hp ha.running (by decide : 0≤272)) fun b hb=>?_)
  refine WP.seq (WP.mono (flagsStage_ok hp hb) fun c ⟨hc,hflag⟩=>?_)
  change WP isa (.seq (secondBatch sha3 η) _) c _
  refine WP.seq (WP.mono (secondBatch_ok sha3 hη hp hc hflag) fun d ⟨A,hd,hdf⟩=>?_)
  change WP isa (.seq maskFour _) d _
  refine WP.seq (WP.mono (maskStage_ok hp hd hdf) fun e he=>?_)
  exact finish_ok hp he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourShake.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

theorem permuted_add (A : Spec.Sha3.State) (i j : Nat) :
    Resident.permuted (Resident.permuted A i) j=Resident.permuted A (i+j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Resident.permuted,ih]; rfl

theorem chunks_squeeze (A : Spec.Sha3.State) :
    chunkBytes A++chunkBytes (Resident.permuted A 2)=
      Spec.Sha3.squeezeBlocks 136 (Spec.Sha3.keccakF A) 4 := by
  apply List.ext_getElem
  · rw [List.length_append,chunkBytes_length,chunkBytes_length,
      VG.Proof.Sha3.length_squeezeBlocks (by decide)]
  · intro j hj hj'
    have hj544 : j<544:=by simpa only [List.length_append,chunkBytes_length] using hj
    rw [VG.Proof.Sha3.getElem_squeezeBlocks (by decide) (by decide),
      VG.Proof.Sha3.iterF_keccakF,←Resident.permuted_eq_iterF]
    by_cases h : j<272
    · rw [List.getElem_append_left (by simpa only [chunkBytes_length] using h)]
      simpa only [getElem!_pos (chunkBytes A) j (by rw [chunkBytes_length]; exact h)] using chunkBytes_get A h
    · rw [List.getElem_append_right (by simpa only [chunkBytes_length] using (by omega_using [h] : 272≤j))]
      simp only [chunkBytes_length]
      rw [←getElem!_pos (chunkBytes (Resident.permuted A 2)) (j-272) (by rw [chunkBytes_length]; omega_using [hj544]),
        chunkBytes_get _ (by omega_using [hj544]),permuted_add]
      have hd : 2+((j-272)/136+1)=j/136+1:=by omega_using [h]
      have hm : (j-272)%136=j%136:=by omega_using [h]
      rw [hd,hm]

theorem chunks_H (m : Mem) (p : Addr) :
    chunkBytes (ResidentMask.seedState m p)++
      chunkBytes (Resident.permuted (ResidentMask.seedState m p) 2)=
      Spec.MlDsa.H (Spec.Sha3.bytesAt m p 66) 544 := by
  rw [chunks_squeeze,ResidentMask.seedState_eq]
  change _=Spec.Sha3.squeeze 136
    (VG.Proof.MlKem.padded 136 Spec.Sha3.shakeSuffix (Spec.Sha3.bytesAt m p 66)) 544
  rw [ResidentSeed66.padded_A0 (VG.Proof.Sha3.bytesAt_length _ _ _),Spec.Sha3.squeeze]
  change _=(Spec.Sha3.squeezeBlocks 136
    (Spec.Sha3.keccakF (ResidentSeed66.A0 (Spec.Sha3.bytesAt m p 66))) 4).take 544
  rw [List.take_of_length_le (by rw [VG.Proof.Sha3.length_squeezeBlocks (by decide)])]

theorem sampledRows_H (σ : State) (η i : Nat) :
    sampledRows σ η i=rbFold η []
      (Spec.MlDsa.H (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) 544) := by
  unfold sampledRows samplerA
  rw [←rbFold_append,chunks_H]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
