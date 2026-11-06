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
  refine WP.mono (widthHeader_ok E rfl) fun v ⟨hm, h16, c0, c1, c2, fv, kv⟩ => ?_
  have wv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kv.wr.trans E.wr
  apply WP.seq
  refine WP.mono (controller_ok h rfl hA (by rw [wv]; exact List.mem_cons_self ..) _ v
    (loop_initial h hm (by simpa [upd] using h16) c0 c1 c2)) fun t hd => ?_
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

end VG.Proof.Dsa.AArch64.Generation.Refill
