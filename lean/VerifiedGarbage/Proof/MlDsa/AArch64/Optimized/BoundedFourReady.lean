import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCounts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSamplerState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair

/-! ## From `BoundedFourCounts.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem initCounts_ok {s : State} {b : Addr} (hb : s.gpr .x19=b)
    (hw : ∀i<4,InRegions s.wr (countAt b i) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      (Keep [.x4] s t ∧
      Frame [⟨b+7904#64,32⟩] s.mem t.mem ∧
      ∀i<4,t.mem.readW (countAt b i) 64=256) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts
  refine wp_movz fun a ha h4=>?_
  refine WP.mono (ResidentRej.countsStore_ok 4 (by decide) (s := a) (p := b)
    (by rw [ha.get .x19]; exact hb) h4 (fun i hi=>by rw [ha.wr]; exact hw i hi))
    fun t ⟨ht,hf,hc⟩=>?_
  refine ⟨?_,?_,hc⟩
  · exact ⟨fun r hr=>by rw [ht.gpr]; exact ha.gpr r hr,
      ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,
      fun r hr=>by rw [ht.vec]; exact ha.vcs r hr⟩
  · rw [ha.mem] at hf
    exact hf

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitTable.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def tableMemory (m : Mem) (p : Addr) : Nat → Mem
 | 0 => m
 | n+1 => initEntryMemory (tableMemory m p n) p n

def TablePrefix (m : Mem) (p : Addr) (n : Nat) : Prop := ∀mask<n,
 m.read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
 m.readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=BitVec.ofNat 64 (acceptedIndices mask).length

theorem tableMemory_prefix (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    TablePrefix (tableMemory m p n) p n := by
  induction n with
  | zero => intro mask hm; omega
  | succ n ih =>
    have hprev := ih (by omega)
    intro mask hm
    by_cases he : mask=n
    · subst mask; exact initEntryMemory_read _ p (by omega)
    · have hother := initEntryMemory_other (tableMemory m p n) p (by omega : n<16) (by omega : mask<16) he
      have hp := hprev mask (by omega)
      exact ⟨hother.1.trans hp.1,hother.2.trans hp.2⟩

theorem TablePrefix.table {m : Mem} {p : Addr} (h : TablePrefix m p 16) : TableAt m (p+6000) := by
  intro mask hm
  have e0 : (p+6000)+BitVec.ofNat 64 (64*mask)=p+BitVec.ofNat 64 (6000+64*mask) := by
    change (p+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*mask)=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have e1 : (p+BitVec.ofNat 64 (6000+64*mask))+32=p+BitVec.ofNat 64 (6000+64*mask+32) := by
    change (p+BitVec.ofNat 64 (6000+64*mask))+BitVec.ofNat 64 32=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [e0,e1]
  exact h mask hm

theorem tableMemory_table (m : Mem) (p : Addr) : TableAt (tableMemory m p 16) (p+6000) :=
  (tableMemory_prefix m p (by decide : 16≤16)).table

def tablePrefixCode (n : Nat) : List Instr := (List.range n).flatMap (entryInit true)

theorem tablePrefixCode_ok {n : Nat} (hn : n≤16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀mask<n,∀off∈[0,8,32],InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+off)) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v → t.mem=tableMemory s.mem (s.gpr .x19) n →
      WP isa (.block rest) t Q) :
    WP isa (.block (tablePrefixCode n++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact k s (Keep.refl _ _) rfl rfl
  | succ n ih =>
    have he : tablePrefixCode (n+1)=tablePrefixCode n++entryInit true n := by
      simp only [tablePrefixCode,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [he,List.append_assoc]
    refine ih (by omega) (by intro mask hm; exact hw mask (by omega)) fun a ha hav ham => ?_
    refine entryInit_ok (by omega) (by
      intro off hoff
      rw [ha.wr,ha.get .x19]
      exact hw n (by omega) off hoff) fun t ht htv htm =>
        k t ((ha.trans ht).mono (by simp)) (htv.trans hav) ?_
    rw [htm,ham,ha.get .x19]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourPro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

theorem samplerPro_ok {σ : State} (hp : SamplerPre σ) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.pro) σ (SamplerEnv σ) :=
  ResidentRej.pro_with 4 (fun _ _ h=>sampler_in_work hp rfl h)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def initTableRegion (p : Addr) : Region := ⟨p+BitVec.ofNat 64 6000,1024⟩

theorem initEntryMemory_tableFrame (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    Frame [initTableRegion p] m (initEntryMemory m p mask) := by
  rw [initEntryMemory_eq m p hm]
  have h16 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask)) 16 :=
    Offset.contains p (by omega) (by omega) (by decide)
  have h32 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 :=
    Offset.contains p (by omega) (by omega) (by decide)
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem tableMemory_frame (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    Frame [initTableRegion p] m (tableMemory m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih => exact (ih (by omega)).trans (initEntryMemory_tableFrame _ p (by omega))

/-- The selected fast initializer builds all sixteen entries, changes only x6,
and confines writes to the 1024-byte table at scratch+6000. -/
theorem tableInit_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀a n,InRegions [initTableRegion (s.gpr .x19)] a n → InRegions s.wr a n)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      TableAt t.mem (s.gpr .x19+6000) →
      Frame [initTableRegion (s.gpr .x19)] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (tableInit true++rest)) s Q := by
  change WP isa (.block (tablePrefixCode 16++rest)) s Q
  refine tablePrefixCode_ok (by decide) (by
    intro mask hm off hoff
    apply hw
    refine ⟨initTableRegion (s.gpr .x19),by simp,?_⟩
    have ho : off=0 ∨ off=8 ∨ off=32 := by simpa using hoff
    exact Offset.contains _ (by omega) (by omega) (by decide)) fun t ht hv hm => k t ht hv ?_ ?_
  · rw [hm]
    exact tableMemory_table _ _
  · rw [hm]
    exact tableMemory_frame _ _ (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAbsorb.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (absorbPair)
open ResidentRej (seedP scr at' scrR stateP)
open ResidentMask (absorbBody_ok seedState_eq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (zeros_ok pair_sub)

def absorbArgs (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66]

theorem absorbPair_eq (p : Nat) : absorbPair p=absorbArgs p++Impl.MlDsa.AArch64.Optimized.ResidentMask.absorbBody := rfl

theorem absorbArgs_ok {p : Nat} (hp : p<2) {s : State} :
    WP isa (.block (absorbArgs p)) s fun t=>Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2=s.gpr .x19+BitVec.ofNat 64 (400*p) ∧
      t.gpr .x3=s.gpr .x20+BitVec.ofNat 64 (132*p) ∧
      t.gpr .x4=s.gpr .x20+BitVec.ofNat 64 (132*p+66) := by
  unfold absorbArgs
  refine Proof.MlKem.AArch64.wp_addImm (by omega) fun a ha h2=>
    Proof.MlKem.AArch64.wp_addImm (by omega) fun b hb h3=>
    Proof.MlKem.AArch64.wp_addImm (by decide) fun t ht h4=>Proof.MlKem.AArch64.wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,hb.get .x2,h2]
  · rw [ht.get .x3,h3,ha.get .x20]
  · rw [h4,h3,ha.get .x20,BitVec.add_assoc,←BitVec.ofNat_add]

private theorem seed_sub {σ : State} {k : Nat} (hk : k<4) :
    Region.Sub (ResidentMask.seedR (seedP σ+BitVec.ofNat 64 (66*k)))
      (samplerSeeds σ) := Offset.sub_base (seedP σ) (by omega)

private theorem seed_eq {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s)
    {k : Nat} (hk : k<4) :
    Spec.Sha3.bytesAt s.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66=Spec.Sha3.bytesAt σ.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66 := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_output.sub_left (seed_sub hk)
  · exact hp.seed_work.sub_left (seed_sub hk)

theorem zeroAll_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => SamplerEnv σ t ∧
      ∀i<50,t.mem.read (wordAddr (scr σ) i) 16=0 := by
  refine WP.mono (zeros_ok he.x19 (fun i hi => sampler_in_work hp he.wr (by omega))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩

theorem absorbPair_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) {p : Nat} (hstream : 2*p+1<4)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => SamplerEnv σ t ∧
      PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  have hpn : p<2 := by omega
  rw [absorbPair_eq,WP.block_append_iff]
  refine WP.mono (absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : SamplerEnv σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := seedP σ+BitVec.ofNat 64 (66*(2*p))
  let b := seedP σ+BitVec.ofNat 64 (66*(2*p+1))
  have e2' : s1.gpr .x2 = stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 132*p = 66*(2*p) by omega]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 132*p+66 = 66*(2*p+1) by omega]
  have seed_in (k : Nat) (hk : k < 4) (d n : Nat) (hd : d+n ≤ 66) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (66*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact sampler_in_seed hp he1.rd (by omega)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    change InRegions s1.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact sampler_in_work hp he1.wr (by omega)
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega)
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega) (8*j) 8 (by omega))
    (fun j hj => seed_in (2*p+1) (by omega) (8*j) 8 (by omega))
    (seed_in (2*p) (by omega) 64 1 (by decide)) (seed_in (2*p) (by omega) 65 1 (by decide))
    (seed_in (2*p+1) (by omega) 64 1 (by decide)) (seed_in (2*p+1) (by omega) 65 1 (by decide))
    hws ((hp.seed_work.sub_left (seed_sub (by omega))).sub_right hps)
    ((hp.seed_work.sub_left (seed_sub (by omega))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega : 2*p < 4),seed_eq hp he1 (by omega : 2*p+1 < 4)] at hp2
    simpa only [samplerA,samplerSeedAt,seedState_eq] using hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourStart.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr)

def samplerInit : List Instr := Impl.MlDsa.AArch64.Sample.Rej4.pro++
 Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 0++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 1

theorem pairs_disjoint (σ : State) : (pairR (stateP σ 0)).Disjoint (pairR (stateP σ 1)) :=
  Offset.disjoint (scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = wordAddr (scr σ) (25*p+i) := by
  change stateP σ p + BitVec.ofNat 64 (16*i) = scr σ + BitVec.ofNat 64 (16*(25*p+i))
  change (scr σ + BitVec.ofNat 64 (400*p)) + BitVec.ofNat 64 (16*i) = _
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem initFour_ok {σ : State} (hp : SamplerPre σ) : WP isa (.block samplerInit) σ fun t => SamplerEnv σ t ∧
    PairAt t.mem (stateP σ 0) (samplerA σ 0) (samplerA σ 1) ∧
    PairAt t.mem (stateP σ 1) (samplerA σ 2) (samplerA σ 3) := by
  unfold samplerInit
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (samplerPro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (absorbPair_ok (p := 0) hp he2 (by decide : 2*0+1 < 4) (fun i hi => by
    rw [state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega))) fun s3 ⟨he3,hp3,hf3⟩ => ?_
  have hz3 : ∀ i < 25,s3.mem.read (wordAddr (stateP σ 1) i) 16 = 0 := by
    intro i hi
    rw [hf3.read (pair_contains (stateP σ 1) hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (pairs_disjoint σ).symm) (by decide),state_word]
    exact hz2 (25+i) (by omega)
  refine WP.mono (absorbPair_ok (p := 1) hp he3 (by decide : 2*1+1 < 4) hz3) fun t ⟨het,hpt,hft⟩ => ?_
  refine ⟨het,?_,hpt⟩
  intro i hi
  rw [hft.read (pair_contains (stateP σ 0) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact pairs_disjoint σ) (by decide)]
  exact hp3 i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourReady.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr lowR)

structure InitialPairs (σ s : State) : Prop where
 env : SamplerEnv σ s
 pair : ∀p<2,PairAt s.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1))

structure Ready (σ s : State) : Prop extends InitialPairs σ s where
 counts : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256
 table : TableAt s.mem (scr σ+6000)

theorem pairs_count_keep {σ s t : State} (hs : InitialPairs σ s)
    (hf : Frame [⟨scr σ+7904#64,32⟩] s.mem t.mem) {p : Nat} (hp : p<2) :
    PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint (scr σ) (d := 400*p) (e := 7904) (n := 400) (k := 32)
      (by omega) (by omega) (by decide)) (by decide)]
  exact hs.pair p hp i hi

theorem initCounts_pairs {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      InitialPairs σ t ∧∀i<4,t.mem.readW (countAt (scr σ) i) 64=256 := by
  refine WP.mono (initCounts_ok hs.env.x19 (fun i hi=>sampler_in_work hp hs.env.wr (by omega)))
    fun t ⟨⟨ht,hf,hc⟩,_⟩=>?_
  refine ⟨⟨?_,fun p hp=>pairs_count_keep hs hf hp⟩,hc⟩
  exact hs.env.lowStep hf (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.sub_base (scr σ) (d := 7904) (n := 32) (k := 7968) (by decide))
    ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> decide))

theorem tableInit_ready {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s)
    (hc : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)) s (Ready σ) := by
  rw [←List.append_nil (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)]
  refine tableInit_ok (fun a n h=>?_) fun t ht hv htable hf=>WP.block_nil_iff.mpr ?_
  · obtain ⟨r,hr,hcontains⟩:=h
    rw [List.mem_singleton.mp hr] at hcontains
    rw [hs.env.x19] at hcontains
    rw [hs.env.wr,hp.wr]
    exact ⟨samplerWorkspace σ,by simp,by
      change (a-scr σ).toNat+n≤8192
      change (a-(scr σ+6000#64)).toNat+n≤1024 at hcontains
      have hadd : a-scr σ=(a-(scr σ+6000#64))+6000#64 := by bv_omega
      rw [hadd]
      rw [BitVec.toNat_add,show (6000#64).toNat=6000 from rfl]
      have hh:=Nat.mod_le ((a-(scr σ+6000#64)).toNat+6000) (2^64)
      omega⟩
  · rw [hs.env.x19] at hf htable
    refine ⟨⟨?_,?_⟩,?_,htable⟩
    · exact hs.env.lowStep hf (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.sub_base (scr σ) (d := 6000) (n := 1024) (k := 7968) (by decide))
        ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl <;> decide))
    · intro p hp i hi
      rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 400*p) (e := 6000) (n := 400) (k := 1024)
          (by omega) (by omega) (by decide)) (by decide)]
      exact hs.pair p hp i hi
    · intro i hi
      rw [hf.readW (Region.contains_self (countAt (scr σ) i) 8) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 7904+8*i) (e := 6000) (n := 8) (k := 1024)
          (by omega) (by omega) (by decide)) (by decide)]
      exact hc i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
