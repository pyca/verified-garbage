module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTClassify
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Correct
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTClassify
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Correct
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with the correctness ones, `Correct`

/-! # The controller's timing depends on its public data and its trace

Two runs that `genContract.pub` relates start at the same point
(`initialPoint`): an iteration takes both to the next point or ends both
(`gen_ct_step`), and every block, call and test between is of the point.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem frame_alloc_ct)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## An iteration -/

theorem search_run_post (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (Two AfterCT) :=
  two_post (search_run_ct v) fun _ s ⟨o, st, ha, hl, hw⟩ =>
    WP.mono (search_run v hl) fun _ h => ⟨o, st, s, ha, hl, hw, h⟩

theorem classify_any [Key.KeyProof] (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (classify keyCall) t (AnyFrame q.inputs) := by
  obtain ⟨o, st, s, -, hl, -, ha⟩ := h
  refine WP.mono (classify_ok ⟨hl, [], rfl⟩ ha) fun u hc => ?_
  rcases hc with ⟨-, -, -, ⟨st', -, hl', -⟩, -⟩ | ⟨-, hd⟩
  · exact ⟨o, _, st', hl'.toGenFrame⟩
  · exact ⟨o, _, _, hd.1⟩

theorem iteration_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (iteration (searchCall v) keyCall) (fun _ _ => True) := by
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  exact RelCT.seq (search_run_post v) (RelCT.seq (two_post classify_ct classify_any)
    (frame_ct (fun _ _ h => h) (by taint_decide)))

/-! ## The loop -/

/-- What each step that goes on lowers. -/
def GenPoint.measure (q : GenPoint) : Nat := (q.inputs.randLen - q.used) * 2 ^ 64 + q.left

theorem next_measure {q : GenPoint} {t : State} (hc : q.continues) (h : GenCTL q.next t) :
    q.next.measure < q.measure := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hle := hl.used_le
  have hlt := hl.state.left_lt
  rw [ha.1] at hlt
  unfold GenPoint.measure
  simp only [GenPoint.next] at hle hlt ⊢
  rcases hc with ⟨h3, hl2⟩ | ⟨h1, hc0, -⟩
  · simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand)) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h3 : ¬q.status = 3 := by omega
    simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t

private theorem iteration_pair [Key.KeyProof] (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (searchCall v) keyCall) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (searchCall v) keyCall) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct v).mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, by rw [hn]; exact next_measure hb c₁, q.next, rfl,
      c₁, c₂⟩⟩
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem loop_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration (searchCall v) keyCall) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-! ## Entry and return -/

/-- The point a run starts at. -/
def initialPoint (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (stackArg s 1) 24, (genResult s).trace⟩

/-- A run's entry at a point. -/
def GenStart (q : GenPoint) (s : State) : Prop := genPre s ∧ initialPoint s = q

/-- A run's entry, past the frame's allocation. -/
def AllocStart (q : GenPoint) (u : State) : Prop := ∃ s, GenStart q s ∧ u = allocated 160 s

/-- The registers past the frame's first words. -/
def EntryPins (q : GenPoint) (t : State) : Prop :=
  t.gpr .rax = q.inputs.stp ∧ t.gpr .r12 = q.inputs.F ∧ t.gpr .rsp = q.inputs.F

theorem alloc_start_pins : Pins AllocStart [.rsp] := by
  rintro q _ _ ⟨s, ⟨h₁, e₁⟩, rfl⟩ ⟨t, ⟨h₂, e₂⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [alloc_rsp (p := q.inputs) ⟨h₁, by rw [← e₁]; rfl⟩, alloc_rsp (p := q.inputs) ⟨h₂, by rw [← e₂]; rfl⟩]

theorem entry_pins (q : GenPoint) (u : State) (h : AllocStart q u) : WP isa (.block entryHead) u (EntryPins q) := by
  obtain ⟨s, ⟨hp, e⟩, rfl⟩ := h
  have hi : GenInput q.inputs s := ⟨hp, by rw [← e]; rfl⟩
  refine WP.mono (entry_head_ok hi) fun t ⟨hr, ha, _, k⟩ => ⟨?_, hr, ?_⟩
  · rw [ha, ← hi.2]; rfl
  · rw [k.gpr (by decide), alloc_rsp hi]

theorem entry_ct : RelCT isa (Two AllocStart) (.block (entryHead ++ entryWords)) (fun _ _ => True) :=
  RelCT.block_append (RelCT.seq (two_piece (Ψ := EntryPins) [.rsp] alloc_start_pins (by taint_decide) entry_pins)
    (two_taint [.rax, .r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)))

/-- Past the entry, at the point. -/
def StartCT (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ GenFrame q.inputs s 0 (genProgress s) t ∧ Frame [q.inputs.frame] s.mem t.mem

theorem entry_post (q : GenPoint) (u : State) (h : AllocStart q u) :
    WP isa (.block (entryHead ++ entryWords)) u (StartCT q) := by
  obtain ⟨s, ⟨hp, e⟩, rfl⟩ := h
  have hi : GenInput q.inputs s := ⟨hp, by rw [← e]; rfl⟩
  exact WP.mono (gen_start hi) fun t ⟨hg, hf⟩ => ⟨s, ⟨hp, e⟩, hg, hf⟩

theorem start_point (q : GenPoint) (t : State) (h : StartCT q t) : WP isa clearAround t (GenCTL q) := by
  obtain ⟨s, ⟨hp, e⟩, hg, hfr⟩ := h
  subst e
  have hf := hg.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  refine WP.mono (clearAround_ok hg ?_) fun w ⟨hw, hfw⟩ => ⟨s, genProgress s, ⟨rfl, rfl, rfl, rfl⟩, hw, ?_⟩
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      exact bytes_kept hfr (hg.frame_key.sub_right (slot_sub _ (by omega))) (by
        show (initialPoint s).inputs.L ≤ 2 ^ 64; have := hf.nK; omega)
  · -- The state's request word, kept through the entry and the clearing.
    have hd : ∀ r ∈ [(⟨(initialPoint s).inputs.kp, 9 * (initialPoint s).inputs.L⟩ : Region),
        (initialPoint s).inputs.frame], (cS (initialPoint s).inputs).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hf.kT.symm
      · exact hg.state_frame.symm
    have h1 := hfw.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
      (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega)) hd
      (by decide)
    have h2 := hfr.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
      (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hg.state_frame.symm) (by decide)
    exact h1.trans h2

theorem clear_around_ct : RelCT isa (Two StartCT) clearAround (fun _ _ => True) :=
  frame_ct (fun _ _ ⟨s, _, hg, _⟩ => ⟨s, _, _, hg⟩) (by taint_decide)

/-- A loop's end. -/
def DoneCT (q : GenPoint) (t : State) : Prop := ∃ original final, GenDone q.inputs original final t

theorem loop_done [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (.loop (iteration (searchCall v) keyCall) .e) s (DoneCT q) := by
  obtain ⟨o, st, -, hl, -⟩ := h
  exact WP.mono (gen_loop v (n := genMeasure q.inputs q.used st)
    (final := (tailOf q.inputs o q.used st).consume q.used []) ⟨q.used, st, rfl, hl, [], rfl⟩)
    fun _ ht => ⟨o, _, ht⟩

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) :=
  frame_ct (fun _ _ ⟨o, _, hd⟩ => ⟨o, _, _, hd.1⟩) (by taint_decide)

/-! ## The whole controller -/

theorem gen_code_ct [Key.KeyProof] (v : RoundImpl) : RelCT isa (Two GenStart) (genCode v) (fun _ _ => True) := by
  unfold genCode code
  apply frame_alloc_ct
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine (RelCT.seq (two_post entry_ct entry_post)
    (RelCT.seq (two_post clear_around_ct start_point)
      (RelCT.seq (two_post (loop_ct v) (loop_done v)) finish_ct))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

theorem initial_point_eq {s t : State} (hp : genPub s t) : initialPoint s = initialPoint t := by
  obtain ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, ha, hw, -, -, -, htr⟩ := hp
  have hj : ∀ j < 7, s.mem.readW (stackArg s 1 + BitVec.ofNat 64 (8 * j)) 64 =
      t.mem.readW (stackArg t 1 + BitVec.ofNat 64 (8 * j)) 64 := fun j hj' => by
    have := congrArg (fun l => l[j]?) hw
    simpa [Spec.Rsa.wordsAt, List.getElem?_map, hj'] using this
  have w0 := hj 0 (by decide)
  have w1 := hj 1 (by decide)
  have w3 := hj 3 (by decide)
  have w4 := hj 4 (by decide)
  have w5 := hj 5 (by decide)
  have w6 := hj 6 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at w0 w1 w3 w4 w5 w6
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  rw [a1] at w0 w1 w3 w4 w5 w6
  have he : genE s = genE t := by
    simp only [genE, Spec.Rsa.bytesAt, a1]
    refine List.map_congr_left fun i hi => ?_
    exact word_bytes (m₁ := s.mem) (m₂ := t.mem) (a := stackArg t 1 + BitVec.ofNat 64 48) w6 (List.mem_range.mp hi)
  have hL : genLen s = genLen t := by
    simp only [genLen, a1]
    exact congrArg BitVec.toNat w1
  have hG : genOfState s = genOfState t := by
    simp only [genOfState, hdi, hdx, hcx, h9, a1, hsp, hL, h8, a0, he]
  have hpw : phaseWord (genProgress s).phase = phaseWord (genProgress t).phase := by
    have e4 : (s.mem.readW (stackArg t 1 + 32) 64).toNat = (t.mem.readW (stackArg t 1 + 32) 64).toNat :=
      congrArg BitVec.toNat w4
    simp only [genProgress, keyProgressAt, a1, e4]
    split <;> rfl
  have hl : (genProgress s).left = (genProgress t).left := by
    have e5 : (s.mem.readW (stackArg t 1 + 40) 64).toNat = (t.mem.readW (stackArg t 1 + 40) 64).toNat :=
      congrArg BitVec.toNat w5
    simp only [genProgress, keyProgressAt, a1, e5]
  have hr : (genProgress s).remaining = (genProgress t).remaining := by
    have e0 : (s.mem.readW (stackArg t 1) 64).toNat = (t.mem.readW (stackArg t 1) 64).toNat :=
      congrArg BitVec.toNat w0
    simp only [genProgress, keyProgressAt, a1, e0]
  simp only [initialPoint, hG, hpw, hl, hr, htr, Bignum.word, off, a1]
  rw [w3]

theorem gen_constantTime [Key.KeyProof] (v : RoundImpl) :
    ConstantTime isa genContract.pre genContract.pub (genCode v) := by
  refine RelCT.constantTime ((gen_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨initialPoint s, ⟨hs, rfl⟩, ⟨ht, (initial_point_eq hp).symm⟩⟩

end VG.Proof.RsaKeyGen.X86_64.Generate
