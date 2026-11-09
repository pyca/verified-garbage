module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTClassify
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTClassify
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # RSA key generation's controller on AArch64: constant time

Two runs whose public data agree start at the same point (`initialPoint`):
the same public descriptor, progress words, request word and key search
trace. Each iteration takes them to the same next point or both out of the
loop (`gen_ct_step`), and every block, call and test between is of the
point.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## The key's buffer cleared but `p` -/

theorem clearAround_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → AnyFrame (f a) s) : RelCT isa (Two Φ) clearAround fun _ _ => True := by
  unfold clearAround
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).kp, 4 * (f a).L) s)
    (frame_ct f (fun a s h => (hΦ a s h).x19) (by taint_decide)) fun a s h => ?_)
    (RelCT.seq (two_post (Ψ := fun a s => AnyFrame (f a) s)
      (two_map (fun a => (f a, (f a).kp, 4 * (f a).L)) (fun _ _ h => h) clear_ct) fun a s h => clear_post _ s h)
    (RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).slot 5, 4 * (f a).L) s)
      (frame_ct f (fun a s h => h.x19) (by taint_decide)) fun a s h => ?_)
      (two_map (fun a => (f a, (f a).slot 5, 4 * (f a).L)) (fun _ _ h => h) clear_ct)))
  · obtain ⟨o, u, st, g⟩ := hΦ a s h
    obtain ⟨hL1, hL2, -⟩ := g.len_valid
    have h4 : BitVec.ofNat 64 (f a).L <<< 2 = BitVec.ofNat 64 (4 * (f a).L) := by
      rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
    refine WP.mono (setLow_ok g) fun t ⟨hm, k⟩ => ?_
    obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
    rw [h4] at w13
    exact ⟨o, u, st, g', w12, w13, by
      rw [g.key_region]; exact Region.sub_prefix (by show 4 * (f a).L ≤ 9 * (f a).L; omega),
      by show 1 ≤ 4 * (f a).L; omega, by show 4 * (f a).L < 2 ^ 63; omega⟩
  · obtain ⟨o, u, st, g⟩ := h
    obtain ⟨hL1, hL2, -⟩ := g.len_valid
    have h4 : BitVec.ofNat 64 (f a).L <<< 2 = BitVec.ofNat 64 (4 * (f a).L) := by
      rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
    have h5 : (f a).kp + (BitVec.ofNat 64 (f a).L <<< 2 + BitVec.ofNat 64 (f a).L) = (f a).slot 5 := by
      rw [h4, SearchInit.add_ofNat]; congr 2; omega
    refine WP.mono (setHigh_ok g) fun t ⟨hm, k⟩ => ?_
    obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
    rw [h4] at w13
    rw [h5] at w12
    exact ⟨o, u, st, g', w12, w13, by
      rw [g.key_region]; exact slot_sub _ (by show 5 * (f a).L + 4 * (f a).L ≤ 9 * (f a).L; omega),
      by show 1 ≤ 4 * (f a).L; omega, by show 4 * (f a).L < 2 ^ 63; omega⟩

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
  simp only [VG.Impl.Bignum.AArch64.seqs]
  exact RelCT.seq (search_run_post v) (RelCT.seq (two_post classify_ct classify_any)
    (frame_ct (fun q : GenPoint => q.inputs) (fun _ _ h => h.x19) (by taint_decide)))

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

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t ∧ s.sp = t.sp

private theorem iteration_pair [Key.KeyProof] (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (searchCall v) keyCall) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧ (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (searchCall v) keyCall) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct v).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩)
    (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, by rw [hn]; exact next_measure hb c₁, q.next, rfl,
      c₁, c₂, hsp⟩⟩
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem loop_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration (searchCall v) keyCall) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- The point a run starts at. -/
def initialPoint (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (s.gpr .x7) 24, (genResult s).trace⟩

/-- A run's entry at a point. -/
def GenStart (q : GenPoint) (s : State) : Prop := genPre s ∧ initialPoint s = q

theorem GenStart.input {q : GenPoint} {s : State} (h : GenStart q s) : GenInput q.inputs s :=
  ⟨h.1, by rw [← h.2]; rfl⟩

/-- A run's entry, past the frame's allocation. -/
def AllocStart (q : GenPoint) (u : State) : Prop := ∃ s, GenStart q s ∧ u = allocated 160 s

theorem entry_ct : RelCT isa (Two AllocStart) (.block entry) (fun _ _ => True) := by
  refine two_taint [.x7] ?_ (by taint_decide)
  rintro q _ _ ⟨s, h₁, rfl⟩ ⟨t, h₂, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  show s.gpr .x7 = t.gpr .x7
  have e₁ : (genOfState s).stp = q.inputs.stp := by rw [← h₁.2]; rfl
  have e₂ : (genOfState t).stp = q.inputs.stp := by rw [← h₂.2]; rfl
  exact e₁.trans e₂.symm

/-- After the entry: the frame's words written. -/
def Entered (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ t.gpr .x19 = q.inputs.F ∧ t.mem = writeFrame s.mem q.inputs.F (entryValues s) ∧
    Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t

theorem entry_ready (q : GenPoint) (u : State) (h : AllocStart q u) : WP isa (.block entry) u (Entered q) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact WP.mono (entry_ok hs.input) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, hs, hx, hm, k⟩

/-- Past the entry and the push of `x30`, at the point. -/
def StartCT (q : GenPoint) (x : State) : Prop :=
  ∃ s, GenStart q s ∧ GenFrame q.inputs s 0 (genProgress s) x ∧
    Frame [q.inputs.frame, belowFrame s] s.mem x.mem

theorem start_of {q : GenPoint} {t : State} (h : Entered q t) : StartCT q (pushedX30 t) := by
  obtain ⟨s, hs, hx, hm, k⟩ := h
  obtain ⟨hu, hfu⟩ := gen_start hs.input hx hm k
  exact ⟨s, hs, hu, hfu⟩

theorem start_point (q : GenPoint) (x : State) (h : StartCT q x) : WP isa clearAround x (GenCTL q) := by
  obtain ⟨s, hs, hg, hfr⟩ := h
  have hi := hs.input
  obtain ⟨hp, e⟩ := hs
  subst e
  have hf := hg.input.cfacts
  refine WP.mono (clearAround_ok hg (start_other hi hg hfr)) fun w ⟨hw, hfw⟩ =>
    ⟨s, genProgress s, ⟨rfl, rfl, rfl, rfl⟩, hw, ?_⟩
  -- The state's request word, kept through the push and the clearing.
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hd : ∀ r ∈ [(⟨(initialPoint s).inputs.kp, 9 * (initialPoint s).inputs.L⟩ : Region),
      (initialPoint s).inputs.frame], (cS (initialPoint s).inputs).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hf.kT.symm
    · exact hi.frame_state.symm
  have hd' : ∀ r ∈ [(initialPoint s).inputs.frame, belowFrame s], (cS (initialPoint s).inputs).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hi.frame_state.symm
    · refine sT.sub_right ?_
      show Region.Sub ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩ ⟨s.sp - BitVec.ofNat 64 416, 416⟩
      exact Region.sub_prefix (by decide)
  have h1 := hfw.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
    (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega)) hd
    (by decide)
  have h2 := hfr.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
    (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega)) hd'
    (by decide)
  exact h1.trans h2

/-- A loop's end, with `x30` and the stack pointer back. -/
def DoneCT (q : GenPoint) (x : State) : Prop :=
  ∃ original final d, GenDone q.inputs original final d ∧ x.mem = d.mem ∧ x.rd = d.rd ∧ x.wr = d.wr ∧
    x.gpr .x19 = q.inputs.F

theorem body_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two Entered) (body (searchCall v) keyCall) (fun _ _ => True) := by
  unfold body
  refine Search.relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · have run : ∀ {t : State}, Entered q t → ∃ tr s',
        Exec isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))) (pushedX30 t) tr s' :=
      fun h => by
        obtain ⟨s, hs, hx, hm, k⟩ := h
        obtain ⟨hu, hfu⟩ := gen_start hs.input hx hm k
        obtain ⟨tr, s', e, -⟩ := gen_inner v hs.input hu hfu
        exact ⟨tr, s', e⟩
    exact ⟨run h₁, run h₂⟩
  · refine (RelCT.seq (two_post (clearAround_ct (fun q : GenPoint => q.inputs)
      (fun _ _ ⟨s, _, hg, _⟩ => ⟨s, _, _, hg⟩)) start_point) (loop_ct v)).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨q, start_of h₁, start_of h₂, by simp only [hsp]⟩

theorem body_post [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (t : State) (h : Entered q t) :
    WP isa (body (searchCall v) keyCall) t (DoneCT q) := by
  obtain ⟨s, hs, hx, hm, k⟩ := h
  refine WP.mono (gen_body v hs.input hx hm k) fun u ⟨d, hd, hu⟩ => ?_
  subst hu
  exact ⟨s, _, d, hd, rfl, rfl, rfl, by rw [RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact hd.1.x19⟩

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) := by
  unfold finish
  refine ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.up) [.x19]
    (frame_pins (fun q => q.inputs) fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => h) ?_ (by taint_decide) (by taint_decide)
  rintro q x ⟨o, f, d, hd, hm, hrd, hwr, h19⟩
  refine ⟨h19, by rw [hrd, hwr]; exact hd.1.frame_ld _ (by decide), ?_⟩
  rw [hm]; exact hd.1.headers (2, q.inputs.up) (by simp [GenPublic.headers])

/-! ## The whole controller -/

theorem gen_code_ct [Key.KeyProof] (v : RoundImpl) : RelCT isa (Two GenStart) (genCode v) (fun _ _ => True) := by
  unfold genCode code
  apply RelCT.alloc
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine (RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (body_ct v) (body_post v)) finish_ct)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-- A word's bytes agree where the words do. -/
theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {k : Nat} (hk : k < 8) :
    m₁ (a + BitVec.ofNat 64 k) = m₂ (a + BitVec.ofNat 64 k) := by
  have e : m₁.read a 8 = m₂.read a 8 := h
  rw [← Mem.extractLsb'_read m₁ a hk, ← Mem.extractLsb'_read m₂ a hk, e]

theorem initial_point_eq {s t : State} (hp : genPub s t) : initialPoint s = initialPoint t := by
  obtain ⟨hsp, h0, -, h2, h3, h4, h5, h6, h7, hw, -, -, -, htr⟩ := hp
  have hj : ∀ j < 7, s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 (8 * j)) 64 =
      t.mem.readW (t.gpr .x7 + BitVec.ofNat 64 (8 * j)) 64 := fun j hj' => by
    have := congrArg (fun l => l[j]?) hw
    simpa [Spec.Rsa.wordsAt, List.getElem?_map, hj'] using this
  have w0 := hj 0 (by decide)
  have w1 := hj 1 (by decide)
  have w3 := hj 3 (by decide)
  have w4 := hj 4 (by decide)
  have w5 := hj 5 (by decide)
  have w6 := hj 6 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at w0 w1 w3 w4 w5 w6
  rw [h7] at w0 w1 w3 w4 w5 w6
  have he : genE s = genE t := by
    simp only [genE, Spec.Rsa.bytesAt, h7]
    refine List.map_congr_left fun i hi => ?_
    exact word_bytes (m₁ := s.mem) (m₂ := t.mem) (a := t.gpr .x7 + BitVec.ofNat 64 48) w6 (List.mem_range.mp hi)
  have hL : genLen s = genLen t := by
    simp only [genLen, h7]
    exact congrArg BitVec.toNat w1
  have hG : genOfState s = genOfState t := by
    simp only [genOfState, h0, h2, h3, h4, h5, h6, h7, hsp, hL, he]
  have hpw : phaseWord (genProgress s).phase = phaseWord (genProgress t).phase := by
    have e4 : (s.mem.readW (t.gpr .x7 + 32) 64).toNat = (t.mem.readW (t.gpr .x7 + 32) 64).toNat :=
      congrArg BitVec.toNat w4
    simp only [genProgress, keyProgressAt, h7, e4]
    split <;> rfl
  have hl : (genProgress s).left = (genProgress t).left := by
    have e5 : (s.mem.readW (t.gpr .x7 + 40) 64).toNat = (t.mem.readW (t.gpr .x7 + 40) 64).toNat :=
      congrArg BitVec.toNat w5
    simp only [genProgress, keyProgressAt, h7, e5]
  have hr : (genProgress s).remaining = (genProgress t).remaining := by
    have e0 : (s.mem.readW (t.gpr .x7) 64).toNat = (t.mem.readW (t.gpr .x7) 64).toNat :=
      congrArg BitVec.toNat w0
    simp only [genProgress, keyProgressAt, h7, e0]
  simp only [initialPoint, hG, hpw, hl, hr, htr, Bignum.word, off, h7]
  rw [w3]

theorem gen_constantTime [Key.KeyProof] (v : RoundImpl) :
    ConstantTime isa genContract.pre genContract.pub (genCode v) := by
  refine RelCT.constantTime ((gen_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨initialPoint s, ⟨hs, rfl⟩, ⟨ht, (initial_point_eq hp).symm⟩, hp.1⟩

end VG.Proof.RsaKeyGen.AArch64.Generate
