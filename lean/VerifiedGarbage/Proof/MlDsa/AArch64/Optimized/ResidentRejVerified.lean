import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFirstBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming

/-! ## From `ResidentRejContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

/-- The resident implementation retains the established bounded sampler result. -/
theorem prefixRow_legacy (σ : State) (k : Nat) :
    prefixRow σ k 1008=VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k := by
  unfold prefixRow
  rw [streamBytes_full]

theorem result_legacy {σ t : State} (h : Result 4 σ t) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.post σ t := by
  constructor
  · rw [h.status]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.mask
    have he : ((List.range 4).all fun k =>
        (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length==256)=true ↔
        ∀k<4,(prefixRow σ k 1008).length=256 := by
      simp only [List.all_eq_true,List.mem_range,beq_iff_eq,prefixRow_legacy]
    by_cases hall : ∀k<4,(prefixRow σ k 1008).length=256
    · rw [ite_eq_left hall,ite_eq_left (he.mpr hall)]
      rfl
    · rw [ite_eq_right hall,ite_eq_right (fun hh => hall (he.mp hh))]
      rfl
  · intro k hk hl
    exact stored_polyIs (by simpa only [prefixRow_legacy,polyP,VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP] using h.stored k hk) hl

theorem pre_four {σ : State} (h : (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre σ) : Pre 4 σ := by
  obtain ⟨hr,hw,hsa,hss,has⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_pre σ h
  exact ⟨Or.inr rfl,hr,hw,hsa,hss,has⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTwoContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def twoPreProps (s : State) : Prop := s.rd=[seedsR 2 s] ∧ s.wr=[aR 2 s,scrR s] ∧
  (seedsR 2 s).Disjoint (aR 2 s) ∧ (seedsR 2 s).Disjoint (scrR s) ∧
  (aR 2 s).Disjoint (scrR s)

theorem pre_two {σ : State} (h : (Spec.MlDsa.rejNTT2Contract AArch64.abi).pre σ) : Pre 2 σ := by
  have hp : ∀s,(Spec.MlDsa.rejNTT2Contract AArch64.abi).pre s → twoPreProps s := by
    sig_implies_pre [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,twoPreProps,
      seedsR,aR,scrR,seedP,aP,scr,AArch64.abi,AArch64.argRegs,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP,VG.Proof.MlDsa.AArch64.Sample.Rej4.aP,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.scr,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR]
  obtain ⟨hr,hw,hsa,hss,has⟩ := hp σ h
  exact ⟨Or.inl rfl,hr,hw,hsa,hss,has⟩

theorem two_correct {σ : State} (h : (Spec.MlDsa.rejNTT2Contract AArch64.abi).pre σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ fun t =>
      abiPreserved σ t ∧ Outcome 2 σ t :=
  WP.mono (two_ok (pre_two h)) fun _ ht => ⟨ht.abi,ht.outcome⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejInitialTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Absorbed (v : Nat) (σ s : State) := Env v σ s ∧
  (∀p,2*p+1<v → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
  ∀k<v,s.mem.readW (countP σ k) 64=256

private theorem initial_relCT {v : Nat} {σ τ : State} {P Q : State → Prop} {c : Prog isa}
    (pub : Pub v σ τ) (hc : PointerCT [.x0,.x1,.x2] c)
    (ws : WP isa c σ P) (wt : WP isa c τ Q) :
    RelCT isa (fun s t => s=σ ∧ t=τ) c (fun s t => P s ∧ Q t) := by
  have ct : RelCT isa (fun s t => s=σ ∧ t=τ) c (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    rcases h with ⟨rfl,rfl⟩
    have ha : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2]) s t := by
      refine ⟨pub.2.2.2.1,?_⟩
      simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
      intro r hr
      rcases hr with rfl | rfl | rfl
      · exact pub.1
      · exact pub.2.1
      · exact pub.2.2.1
    exact ⟨hc _ _ _ _ _ _ True.intro True.intro ha es et,True.intro⟩
  exact (ct.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem startFour_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.init++Four.initCounts))
      (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t) :=
  initial_relCT pub startFour_ct (startFour_ok hp) (startFour_ok hq)

theorem startTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.pro++Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
        Impl.MlDsa.AArch64.Sample.Rej4.absorbPair 0++Two.initCounts))
      (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t) :=
  initial_relCT pub startTwo_ct (startTwo_ok hp) (startTwo_ok hq)

theorem firstFour_left_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t)
      (.seq (.seq (.block (Four.squeezeSetup 0 5)) (five .x22 .x24 .x25)) (five .x23 .x26 .x27))
      (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ _ _ h => h) (by taint_decide))
    (fun _ h => WP.assoc' (firstFour_setup_ok hp h.1 h.2.1 h.2.2))
    (fun _ h => WP.assoc' (firstFour_setup_ok hq h.1 h.2.1 h.2.2))

theorem firstTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t)
      (.seq (.block (Two.squeezeSetup 0 5)) (five .x22 .x24 .x25))
      (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1) firstTwo_ct
    (fun _ h => firstTwo_setup_ok hp h.1 h.2.1 h.2.2)
    (fun _ h => firstTwo_setup_ok hq h.1 h.2.1 h.2.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejChecks.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

 def firstChecks (k : Nat) (hk : k<4) : SegmentChecks k 0 168 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

 def secondChecks (k : Nat) (hk : k<4) : SegmentChecks k 504 112 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

 def lastChecks (k : Nat) (hk : k<4) : SegmentChecks k 840 56 := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejPrefixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev PrefixPair (v blocks n : Nat) (σ τ s t : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Rows v blocks τ (fun k => prefixRow τ k n) t

theorem prefixFour_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : ∀k<4,SegmentChecks k off n) :
    RelCT isa (PrefixPair 4 blocks off σ τ) (Four.batch 0 off n)
      (PrefixPair 4 blocks (off+3*n) σ τ) := by
  refine (batchFour_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem prefixTwo_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : ∀k<2,SegmentChecks k off n) :
    RelCT isa (PrefixPair 2 blocks off σ τ) (Two.batch 0 off n)
      (PrefixPair 2 blocks (off+3*n) σ τ) := by
  refine (batchTwo_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem parseFiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t)
      (.seq (Four.batch 0 0 168) (Four.batch 0 504 112))
      (PrefixPair 4 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 4 5 504 σ τ)
  · exact (prefixFour_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) firstChecks).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixFour_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) secondChecks

theorem parseFiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t)
      (.seq (Two.batch 0 0 168) (Two.batch 0 504 112))
      (PrefixPair 2 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 2 5 504 σ τ)
  · exact (prefixTwo_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) (fun k hk => firstChecks k (by omega))).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixTwo_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) (fun k hk => secondChecks k (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejAdaptiveTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Flagged (v blocks n : Nat) (σ s : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Flags v (fun k => prefixRow σ k n) s

theorem flags_zero_eq {v n : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : Flags v (fun k => prefixRow σ k n) s)
    (ht : Flags v (fun k => prefixRow τ k n) t) :
    (s.gpr .x27==0#64)=(t.gpr .x27==0#64) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,hs.zero,ht.zero]
  constructor
  · intro h k hk; rw [←pub.prefix hk n]; exact h k hk
  · intro h k hk; rw [pub.prefix hk n]; exact h k hk

theorem flagsFour_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (PrefixPair 4 blocks n σ τ) (.block Four.flags)
      (fun s t => Flagged 4 blocks n σ s ∧ Flagged 4 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsFour_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 4 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthFour_ct
          (fun _ h => sixthFour_ok hp h) (fun _ h => sixthFour_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixFour_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) lastChecks)
        exact (flagsFour_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveFour_timingDone hp h.1.1 h.1.2,
    adaptiveFour_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem flagsTwo_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (PrefixPair 2 blocks n σ τ) (.block Two.flags)
      (fun s t => Flagged 2 blocks n σ s ∧ Flagged 2 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsTwo_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 2 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthTwo_ct
          (fun _ h => sixthTwo_ok hp h) (fun _ h => sixthTwo_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixTwo_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) (fun k hk => lastChecks k (by omega)))
        exact (flagsTwo_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveTwo_timingDone hp h.1.1 h.1.2,
    adaptiveTwo_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejCleanupTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem failure_ready {v : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : TimingDone v σ s) (ht : TimingDone v τ t)
    (hz : s.gpr .x27≠0#64) : TailReady v σ s ∧ TailReady v τ t := by
  have hn : t.gpr .x27≠0#64 := by
    intro he
    apply hz
    apply hs.done.flags.zero.mpr
    intro k hk
    rw [pub.prefix hk 1008]
    exact ht.done.flags.zero.mp he k hk
  exact ⟨⟨hs.done,hs.bytes hz⟩,⟨ht.done,ht.bytes hn⟩⟩

private theorem finish_ct : PointerCT [.x19]
    (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem cleanupFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) Four.tailZeros
      (fun s t => Done 4 σ s ∧ Done 4 τ t) := by
  unfold Four.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 4) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t)
      (.seq Four.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupFour_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem cleanupTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) Two.tailZeros
      (fun s t => Done 2 σ s ∧ Done 2 τ t) := by
  unfold Two.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 2) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t)
      (.seq Two.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupTwo_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- The exact four-stream implementation leaks only public pointers and the
seed bytes already declared by the shared matrix-sampling contract. -/
theorem four_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Four.code (fun _ _ => True) := by
  unfold Four.code
  apply RelCT.seq (startFour_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.seq (firstFour_left_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveFour_relCT hp hq pub)
  apply RelCT.seq (flagsFour_relCT hp hq pub)
  apply RelCT.seq (adaptiveFour_relCT hp hq pub)
  exact cleanupFinishFour_relCT hp hq pub

/-- The two-stream implementation has the same seed-dependent leakage policy
with its precisely sized two-seed and two-polynomial memory footprint. -/
theorem two_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Two.code (fun _ _ => True) := by
  unfold Two.code
  apply RelCT.seq (startTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (firstTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveTwo_relCT hp hq pub)
  apply RelCT.seq (flagsTwo_relCT hp hq pub)
  apply RelCT.seq (adaptiveTwo_relCT hp hq pub)
  exact cleanupFinishTwo_relCT hp hq pub

theorem four_ct : ConstantTime isa (Pre 4) (Pub 4) Four.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (four_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

theorem two_ct : ConstantTime isa (Pre 2) (Pub 2) Two.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (two_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem four_verified : Verified target Four.code (Spec.MlDsa.rejNTT4Contract abi) := by
  refine ⟨?_,?_,(VG.Proof.MlDsa.AArch64.Sample.Rej4.verified true).2.2⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := four_ok (pre_four hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 4 s t := by
      sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact four_ct _ _ _ _ _ _ (pre_four hs) (pre_four ht) pub es et

 def twoSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,68⟩]
  wr := [⟨0x2000,2048⟩,⟨0x4000,8192⟩]

 theorem two_verified : Verified target Two.code (Spec.MlDsa.rejNTT2Contract abi) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := two_ok (pre_two hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 2 s t := by
      sig_pub [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact two_ct _ _ _ _ _ _ (pre_two hs) (pre_two ht) pub es et
  · sig_implies_sat [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs]
      [twoSat] using twoSat

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
