module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySavedAbi
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryRestore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryLink
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Words

/-! # The refillable-tape search on AArch64 meets its contract's functional part

The entry, the search for the width in `state[1]` (the controller and its
end), and the restored registers (`refill_correct`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Proof.Dsa.AArch64.Generation

/-! ## The words written -/

theorem written_state (m : Mem) {St U : Addr} (hd : (⟨U, 8⟩ : Region).Disjoint ⟨St, 32⟩) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) St 4 =
      [r0, m.readW (St + BitVec.ofNat 64 8) 64, m.readW (St + BitVec.ofNat 64 16) 64, r3] := by
  have hf : Frame [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m (written m St U r0 r3 uv) := by
    unfold written
    exact (((Frame.refl [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m).writeW (List.mem_cons_self ..) r0
      (Region.contains_self St 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) r3 (Region.contains_self (off St 24) 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) uv (Region.contains_self U 8)
  have mid : ∀ d, 8 ≤ d → d + 8 ≤ 24 → (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 d) 64 =
      m.readW (St + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base St h₁ (by omega)
      · exact Offset.disjoint St (d := d) (e := 24) (by omega) (by omega) (by omega)
      · exact (hd.symm.sub_left (Offset.sub_base St (by omega))) ) (by decide)
  have uSt : Mem.Sep St 8 U 8 := hd.symm.sep (contains_head _ (by decide)) (contains_head _ (by decide))
  have uSt24 : Mem.Sep (off St 24) 8 U 8 := hd.symm.sep (Offset.contains_base _ (by decide) (by decide))
    (contains_head _ (by decide))
  change [(written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 0) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 8) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 16) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 24) 64] = _
  rw [mid 8 (by decide) (by decide), mid 16 (by decide) (by decide), show St + BitVec.ofNat 64 0 = St from BitVec.add_zero St]
  unfold written
  rw [Mem.readW_writeW_sep uSt (by decide), Mem.readW_writeW_sep (Offset.sep_base St (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64, show St + BitVec.ofNat 64 24 = off St 24 from rfl, Mem.readW_writeW_sep uSt24 (by decide),
    Mem.readW_writeW_self64]

theorem written_used (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) U 1 = [uv] := by
  change [(written m St U r0 r3 uv).readW (U + BitVec.ofNat 64 0) 64] = _
  rw [show U + BitVec.ofNat 64 0 = U from BitVec.add_zero U]
  exact congrArg (· :: []) (Mem.readW_writeW_self64 _ _ _)

theorem wordsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) (hn : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (d := 8 * i) (n := 8) (k := 8 * n) (by omega) (by omega)) hd (by decide)

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- The saved registers' slots. -/
def savedRegion : Region := ⟨off (refillBase s₀) 296, 152⟩

/-- What the entry and the search may write. -/
def bodyRegions : List Region :=
  ⟨refillBase s₀, frameBytes⟩ :: ctlRegion (refillBase s₀) :: (refillContext h).changed ++ [inState s₀, inUsed s₀, inOut s₀]

theorem saved_body : ∀ r ∈ bodyRegions h, (savedRegion (s₀ := s₀)).Disjoint r := by
  intro r hr
  simp only [bodyRegions, GenerationContext.changed, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  have st : ∀ {q : Region}, (q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inRand s₀ ∨ q = inScr s₀ ∨ q = inState s₀) →
      (savedRegion (s₀ := s₀)).Disjoint q := fun hq => (h.frame_disjoint hq (by decide)).symm
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base (refillBase s₀) (by decide) (by have := refillBase_bound h; omega)
  · exact Offset.disjoint (refillBase s₀) (d := 296) (e := 448) (by omega) (by omega) (by omega)
  · exact (st (by simp)).sub_right h.arena_sub
  · exact Offset.disjoint_base (refillBase s₀) (by decide) (by have := refillBase_bound h; omega)
  · exact Offset.disjoint_below (refillBase s₀) (by omega)
  · exact st (by simp)
  · exact st (by simp)
  · exact st (by simp)

/-- The search's results. -/
def SearchPost (u t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (s₀.gpr .x1).toNat 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 8) 64, s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h))] ∧
  Frame (bodyRegions h) u.mem t.mem ∧ t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr

/-- What the entry and the controller may write. -/
def priorRegions : List Region :=
  savedRegion (s₀ := s₀) :: ⟨refillBase s₀, frameBytes⟩ :: ctlRegion (refillBase s₀) :: (refillContext h).changed

theorem buffer_prior {q : Region} (hq : q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inState s₀) :
    ∀ r ∈ priorRegions h, q.Disjoint r := by
  have hq' : q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inRand s₀ ∨ q = inScr s₀ ∨ q = inState s₀ := by
    rcases hq with e | e | e <;> simp [e]
  have scr : q.Disjoint (inScr s₀) := by
    rcases hq with rfl | rfl | rfl
    · exact h.outScr
    · exact h.usedScr
    · exact h.scrState.symm
  intro r hr
  simp only [priorRegions, savedRegion, GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.frame_disjoint hq' (by decide)
  · simpa only [off, BitVec.add_zero] using h.frame_disjoint hq' (d := 0) (n := frameBytes) (by decide)
  · exact h.frame_disjoint hq' (by decide)
  · exact scr.sub_right h.arena_sub
  · show q.Disjoint ⟨refillBase s₀, frameBytes⟩
    simpa only [off, BitVec.add_zero] using h.frame_disjoint hq' (d := 0) (n := frameBytes) (by decide)
  · change q.Disjoint (below (refillBase s₀) 272)
    rw [refillBase_below s₀ (by decide)]
    exact (h.stack_disjoint (by decide) hq').symm

theorem search_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {W : Nat → BitVec 64} {u : State}
    (E : EntryDone h W u)
    (fs : Frame [savedRegion (s₀ := s₀), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem u.mem) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.search H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) u (SearchPost h u) := by
  have hA : AttemptOk h (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) :=
    fun hs W t seed hin hm hlen hseed h1 used h16 hu => refillAttempt_ok H G T hm hin seed hlen hseed h1 h16 hu
  simp only [Impl.Dsa.AArch64.Generation.Refill.search, Impl.Dsa.AArch64.Generation.Refill.controller,
    VG.Impl.Bignum.AArch64.seqs]
  apply WP.seq
  refine WP.mono (widthHeader_ok E rfl) fun v ⟨hm, h16, h10, c0, c1, c2, fv, kv⟩ => ?_
  have wv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kv.wr.trans E.wr
  apply WP.seq
  refine WP.mono (controller_ok h hA (by rw [wv]; exact List.mem_cons_self ..) _ _ v
    (loop_initial h hm (by simpa [upd] using h16) (by simpa [upd] using h10) c0 c1 c2)) fun t ⟨_, _, hd⟩ => ?_
  refine WP.mono (finish_ok h wv hd) fun t' F' => ?_
  obtain ⟨m₁, r0, r3, uv, fm₁, e0, e3, eu, ft, x0, bytes, sp', rd', wr'⟩ := F'
  have fs₁ : Frame (priorRegions h) s₀.mem m₁ := by
    have a : Frame (priorRegions h) s₀.mem u.mem := fs.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have b : Frame (priorRegions h) u.mem v.mem := fv.mono fun r hr => by
      rcases List.mem_singleton.mp hr with rfl
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have c : Frame (priorRegions h) v.mem m₁ := fm₁.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    exact (a.trans b).trans c
  have stateM : ∀ d, d + 8 ≤ 32 → m₁.readW (s₀.gpr .x7 + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 d) 64 := fun d hd8 =>
    fs₁.readW (r := inState s₀) (Offset.contains_base _ (d := d) (n := 8) (k := 32) hd8 (by omega))
      (buffer_prior h (by simp)) (by decide)
  have finalD : ∀ {q : Region}, (q = inUsed s₀ ∨ q = inState s₀) →
      ∀ r ∈ [(⟨refillBase s₀, frameBytes⟩ : Region), inOut s₀], q.Disjoint r := by
    intro q hq r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact buffer_prior h (by rcases hq with e | e <;> simp [e]) _ (by simp [priorRegions])
    · rcases hq with rfl | rfl
      · exact h.outUsed.symm
      · exact h.outState.symm
  have ctlState : ∀ {q : Region}, (q = inUsed s₀ ∨ q = inState s₀) → q.Disjoint ⟨off (refillBase s₀) 472, 8⟩ :=
    fun hq => h.frame_disjoint (by rcases hq with e | e <;> simp [e]) (by decide)
  have usedState : (⟨s₀.gpr .x2, 8⟩ : Region).Disjoint ⟨s₀.gpr .x7, 32⟩ := h.usedState
  refine ⟨x0, bytes, ?_, ?_, ?_, sp'.trans E.layout.sp.symm, rd'.trans kv.rd, wr'.trans kv.wr⟩
  · rw [wordsAt_frame ft (n := 1) (finalD (Or.inl rfl)) (by decide)]
    rw [show ∀ m x, Spec.Rsa.wordsAt (Mem.writeW m (off (refillBase s₀) 472) x) (s₀.gpr .x2) 1 =
        Spec.Rsa.wordsAt m (s₀.gpr .x2) 1 from fun m x =>
      wordsAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) x (Region.contains_self _ _))
        (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctlState (Or.inl rfl)) (by decide)]
    rw [written_used, eu]
  · rw [wordsAt_frame ft (n := 4) (finalD (Or.inr rfl)) (by decide)]
    rw [show ∀ m x, Spec.Rsa.wordsAt (Mem.writeW m (off (refillBase s₀) 472) x) (s₀.gpr .x7) 4 =
        Spec.Rsa.wordsAt m (s₀.gpr .x7) 4 from fun m x =>
      wordsAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) x (Region.contains_self _ _))
        (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctlState (Or.inr rfl)) (by decide)]
    rw [written_state _ usedState, e0, e3, stateM 8 (by decide), stateM 16 (by decide)]
  · have b : Frame (bodyRegions h) u.mem v.mem := fv.mono fun r hr => by
      rcases List.mem_singleton.mp hr with rfl
      exact List.mem_cons_self ..
    have c : Frame (bodyRegions h) v.mem m₁ := fm₁.mono fun r hr => by
      simp only [bodyRegions, List.cons_append]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hr)
    have d : Frame (bodyRegions h) m₁ t'.mem := by
      refine ((results_frame m₁ _ _ _ _ _ _ _).mono ?_).trans (ft.mono ?_)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [bodyRegions, List.cons_append]
        rcases hr with rfl | rfl | rfl
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..)))
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [bodyRegions, List.cons_append]
        rcases hr with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    exact (b.trans c).trans d
end

theorem EntryDone.congr {pBytes : Nat} {s₀ : State} {h : RefillABI pBytes s₀} {W : Nat → BitVec 64} {v t : State}
    (E : EntryDone h W v) (hm : t.mem = v.mem) (hk : Keep [.x3, .x4] v t) : EntryDone h W t := by
  obtain ⟨V, R⟩ := E.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W := hm ▸ R
  exact ⟨lay_of_rep E.layout R Rt rfl hk.sp hk.wr, ⟨V, Rt⟩, E.slots, E.w16, E.w10, E.scratch.congr hk.wr,
    ⟨by rw [hk.rd, hk.wr]; exact E.rand.cover, by rw [hm]; exact E.rand.bytes⟩,
    hk.wr.trans E.wr, hk.rd.trans E.rd, by rw [hm]; exact E.c0, by rw [hm]; exact E.c1, by rw [hm]; exact E.c2⟩

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem linkAllocated : RefillAllocated h (linkState s₀) where
  sp := rfl
  wr := rfl
  rd := rfl
  regs := fun r hr => by
    have : r ≠ .x9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [linkState, this]
  mem := link_frame s₀

/-- The body's results, with the saved registers restored. -/
def BodyPost (t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (s₀.gpr .x1).toNat 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 8) 64, s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h))] ∧
  (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧
  (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
  t.sp = refillBase s₀ ∧ t.rd = s₀.rd ∧ t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr

theorem body_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    WP isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 s₀) (BodyPost h) := by
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  unfold Impl.Dsa.AArch64.Generation.entryBody
  refine WP.seq (WP.mono (entrySave_ok s₀) fun u hu => ?_)
  subst hu
  have a := linkAllocated h
  refine WP.seq (WP.mono (entry_ok h a) fun v ⟨W, E, fE, kE⟩ => ?_)
  have h17 : W 17 = BitVec.ofNat 64 pBytes := E.slots 17 (by simp [generationSlots]) (by decide) (by decide)
  obtain ⟨V, R⟩ := E.rep
  apply WP.seq
  refine dispatch_ok H.sha1 H.sha256 G.run T.run E.layout R hp3 h17 fun t hm hk => ?_
  have E' := E.congr hm hk
  have fs : Frame [savedRegion (s₀ := s₀), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem t.mem := by
    rw [hm]
    exact (a.mem.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..).trans
      (fE.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.mono (search_ok h H G T E' fs) fun t₁ ⟨x0, bytes, used, words, ft, sp₁, rd₁, wr₁⟩ => ?_
  -- the saved registers
  have fl : Frame (bodyRegions h) (linkState s₀).mem t₁.mem := by
    refine (fE.mono fun r hr => ?_).trans (hm ▸ ft)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have sep := saved_body h
  have g := (link_gprs s₀).frame_in (lo := 296) (n := 152) (by decide) fl sep
  have vv := (link_vectors s₀).frame_in (lo := 296) (n := 152) (by decide) fl sep
  have lr : t₁.mem.readW (refillBase s₀ + BitVec.ofNat 64 296) 64 = s₀.gpr .x30 := by
    have hc : (savedRegion (s₀ := s₀)).Contains (off (refillBase s₀) 296) 8 := by
      have := Offset.contains_base (off (refillBase s₀) 296) (d := 0) (n := 8) (k := 152) (by decide) (by decide)
      simpa only [savedRegion, off, BitVec.add_zero] using this
    rw [fl.readW hc sep (by decide)]
    exact word_writeW_self (savedAbiMem s₀) (refillBase s₀) 296 (s₀.gpr .x30)
  have sp₁' : t₁.sp = refillBase s₀ := sp₁.trans (hk.sp.trans E.layout.sp)
  have wr₁' : t₁.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := wr₁.trans (hk.wr.trans E.wr)
  have perm (d : Nat) (hd : d + 8 ≤ 480) : InRegions (t₁.rd ++ t₁.wr) (refillBase s₀ + BitVec.ofNat 64 d) 8 := by
    rw [wr₁']
    exact ⟨⟨refillBase s₀, 480⟩, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ hd (by omega)⟩
  refine WP.mono (entryRestore_ok sp₁' perm g vv lr) fun t₂ hv => ?_
  refine ⟨hv.result.trans x0, hv.memory ▸ bytes, hv.memory ▸ used, hv.memory ▸ words, hv.gprs, hv.vectors,
    hv.stack.trans sp₁', hv.read.trans (rd₁.trans (hk.rd.trans E.rd)), hv.write.trans wr₁'⟩

end

/-! ## Correctness -/

theorem refill_correct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (s : State) (pre : (Spec.Dsa.parameterSearchContract abi refillStack).pre s) :
    ∃ tr t, Exec isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) s tr t ∧
      abiPreserved s t ∧ (Spec.Dsa.parameterSearchContract abi refillStack).post s t := by
  have h := refillABI_of pre
  obtain ⟨tr, t, he, x0, bytes, used, words, gp, vp, tsp⟩ :
      WP isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) s fun t =>
        t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
          ((expectedOf (total h)).map (Spec.Dsa.encodeParams (refillPLen s)
            (Spec.Dsa.generationQLen (refillPLen s)))).getD (List.replicate (s.gpr .x1).toNat 0) ∧
        Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
        Spec.Rsa.wordsAt t.mem (s.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
          s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64, s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 16) 64,
          BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested (refillPLen s) (total h))] ∧
        (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
        (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ t.sp = s.sp := by
    unfold Impl.Dsa.AArch64.Generation.code
    apply alloc_frame_ok (bytes := 480) (by decide) (by have := h.stackLower; unfold refillStack at this; omega)
    refine WP.mono (body_ok h H G T) ?_
    intro t ⟨x0, bytes, used, words, gp, vp, sp, _, wr⟩
    refine ⟨by simp only [allocState]; exact sp, by simp only [allocState]; exact wr, ?_⟩
    simp only [freeState]
    refine ⟨x0, bytes, used, words, gp, vp, ?_⟩
    change t.sp + BitVec.ofNat 64 480 = s.sp
    rw [sp]; exact BitVec.sub_add_cancel ..
  refine ⟨tr, t, he, ⟨gp, tsp, vp⟩, ?_⟩
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  have ht : Spec.Dsa.parameterSearch (refillPLen s) (s.mem.readW (s.gpr .x7) 64).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = total h := rfl
  have w8 : s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (refillPLen s) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  have w16 : s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s)) := h.budget
  have hp : 0 < refillPLen s := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  change (BitVec.setWidth 32 (t.gpr .x0)).toNat = (total h).status ∧
    (Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat = match (total h).outcome with
      | .accepted a => Spec.Dsa.encodeParams (refillPLen s) (Spec.Dsa.generationQLen (refillPLen s)) a
      | _ => List.replicate (s.gpr .x1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
      ∃ requested, Spec.Rsa.wordsAt t.mem (s.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
        BitVec.ofNat 64 (refillPLen s), BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s)),
        BitVec.ofNat 64 requested] ∧ (total h).Requests (Spec.Dsa.parameterEntropy (refillPLen s)) requested
  refine ⟨?_, ?_, used, VG.Proof.Dsa.Generation.requested (refillPLen s) (total h), ?_,
    VG.Proof.Dsa.Generation.requested_requests hp _ _⟩
  · have hs : (total h).status < 4 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    rw [x0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [bytes]
    unfold expectedOf
    generalize (total h).outcome = o
    cases o <;> rfl
  · rw [words, w8, w16]

end VG.Proof.Dsa.AArch64.Generation.Refill
