module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTCalls
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTCalls
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # The classification's timing (AArch64)

After the search, every block's addresses are the frame's, the state's
pointer the frame holds, or the region to zero the frame holds; every test is
of the point's status, consumption, generations left, phase or key status.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem ev_false {r : Reg} {s : State} {b : Prop} [Decidable b]
    (he : isa.eval (.zero .x r) s = some (decide b)) (hf : isa.eval (.zero .x r) s = some false) : ¬b := fun h => by
  have hx : some (decide b) = some false := he.symm.trans hf
  simp [h] at hx

/-- The frame's base and the state's pointer in the frame. -/
def Hdr7 (p : GenPublic) (s : State) : Prop :=
  s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 7)) 8 ∧
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * 7)) 64 = p.stp

/-! ## Blocks of the frame and the state -/

theorem nextPrime_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → Hdr7 (f a) s)
    {phase : Nat} (hph : phase < 2) : RelCT isa (Two Φ) (.block (nextPrime phase)) fun _ _ => True := by
  obtain rfl | rfl : phase = 0 ∨ phase = 1 := by omega
  all_goals
  unfold nextPrime
  exact ldf_then (by decide) (fun a => (f a).F) (fun a => (f a).stp) [.x19] (frame_pins f fun a s h => (hΦ a s h).1)
    hΦ (by taint_decide) (by taint_decide)

theorem finishWith_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → Hdr7 (f a) s)
    {status : Nat} (hs : status < 4) : RelCT isa (Two Φ) (.block (finishWith status)) fun _ _ => True := by
  obtain rfl | rfl | rfl | rfl : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 := by omega
  all_goals
  unfold finishWith
  exact ldf_then (by decide) (fun a => (f a).F) (fun a => (f a).stp) [.x19] (frame_pins f fun a s h => (hΦ a s h).1)
    hΦ (by taint_decide) (by taint_decide)

/-- Before `clear`: the region to zero, `len` octets at `op` in the key's
buffer, in the frame's words 12 and 13. -/
def ClearCT (a : GenPublic × Addr × Nat) (s : State) : Prop :=
  ∃ original used st, GenFrame a.1 original used st s ∧ word s.mem a.1.F (8 * 12) = a.2.1 ∧
    word s.mem a.1.F (8 * 13) = BitVec.ofNat 64 a.2.2 ∧ Region.Sub ⟨a.2.1, a.2.2⟩ (inKey original) ∧
    1 ≤ a.2.2 ∧ a.2.2 < 2 ^ 63

theorem clear_ct : RelCT isa (Two ClearCT) clear fun _ _ => True := by
  unfold clear
  refine RelCT.seq (two_piece (Ψ := fun a t => t.gpr .x1 = a.2.1 + BitVec.ofNat 64 0 ∧
    t.gpr .x2 = BitVec.ofNat 64 a.2.2) [.x19] (frame_pins Prod.fst fun _ _ ⟨_, _, _, g, _⟩ => g.x19)
    (by taint_decide) fun a s ⟨o, u, st, g, h12, h13, _⟩ => ?_) (two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide))
  have hl := g.frame_ld
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13
  brun [ldf, g.x19, imm64 (show 0 < 65536 by decide), hl 96 (by decide), hl 104 (by decide), h12, h13]

theorem clear_post (a : GenPublic × Addr × Nat) (s : State) (h : ClearCT a s) :
    WP isa clear s fun t => AnyFrame a.1 t := by
  obtain ⟨o, u, st, g, h12, h13, hsub, h1, hlt⟩ := h
  exact WP.mono (clear_ok g h12 h13 hsub h1 hlt) fun t ⟨g', _⟩ => ⟨o, u, st, g'⟩

theorem fail_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → AnyFrame (f a) s)
    {status : Nat} (hs : status < 4) : RelCT isa (Two Φ) (fail status) fun _ _ => True := by
  unfold fail clearAll
  refine RelCT.seq (RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).kp, 9 * (f a).L) s)
    (frame_ct f (fun a s h => (hΦ a s h).x19) (by taint_decide)) fun a s h => ?_)
    (two_post (two_map (fun a => (f a, (f a).kp, 9 * (f a).L)) (fun _ _ h => h) clear_ct)
      fun a s h => clear_post _ s h)) (finishWith_ct f (fun _ _ h => h.stp) hs)
  obtain ⟨o, u, st, g⟩ := hΦ a s h
  obtain ⟨hL1, hL2, -⟩ := g.len_valid
  have h9 : BitVec.ofNat 64 (f a).L <<< 3 + BitVec.ofNat 64 (f a).L = BitVec.ofNat 64 (9 * (f a).L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]; congr 1; omega
  refine WP.mono (setAll_ok g) fun t ⟨hm, k⟩ => ?_
  obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
  rw [h9] at w13
  exact ⟨o, u, st, g', w12, w13, by rw [g.key_region]; exact fun _ h => h, by show 1 ≤ 9 * (f a).L; omega,
    by show 9 * (f a).L < 2 ^ 63; omega⟩

/-! ## After the search -/

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ AfterSearch q.inputs original q.used st s t

/-- After the search and the count of its octets, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st, AtPoint q original st ∧
    Mid q.inputs original ((tailOf q.inputs original q.used st).consume q.used []) q.used st u

theorem MidCT.any {q : GenPoint} {u : State} (h : MidCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, hm⟩ := h; ⟨o, _, _, hm.frame⟩

theorem status_cases (r : PrimeSearchResult) : r.status = 0 ∨ r.status = 1 ∨ r.status = 3 := by
  rw [rOf_status]; cases r.outcome <;> simp [Spec.Entropy.Outcome.status]

theorem MidCT.status {q : GenPoint} {u : State} (h : MidCT q u) : q.status = 0 ∨ q.status = 1 ∨ q.status = 3 := by
  obtain ⟨o, st, ha, -⟩ := h
  rw [← ha.status]; exact status_cases _

/-- The frame's base and `used`'s pointer in the frame. -/
def Hdr2 (p : GenPublic) (s : State) : Prop :=
  s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 2)) 8 ∧
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * 2)) 64 = p.up

/-- The head's tests, at the point. -/
def HeadCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .x9 = BitVec.ofNat 64 q.status ∧ u.gpr .x10 = BitVec.ofNat 64 q.cand

theorem head_ct : RelCT isa (Two AfterCT) (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8,
    .add .x .x12 .x12 .x10, stf .x12 8]) (Two HeadCT) := by
  have hpin : Pins AfterCT [.x19] :=
    frame_pins (fun q => q.inputs) fun _ _ ⟨_, _, _, _, _, _, ha⟩ => ha.frame.x19
  have hct : RelCT isa (Two AfterCT) (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8,
      .add .x .x12 .x12 .x10, stf .x12 8]) fun _ _ => True := by
    change RelCT isa (Two AfterCT) (.block ([.addImm .w .x9 .x0 0] ++ (ldf .x11 2 :: [ld .x10 .x11, ldf .x12 8,
      .add .x .x12 .x12 .x10, stf .x12 8]))) _
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => Hdr2 q.inputs t) [.x19] hpin (by taint_decide)
      fun q t ⟨o, st, s, _, _, _, ha⟩ => ?_) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.up)
        [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.1) (fun _ _ h => h) (by taint_decide)
        (by taint_decide)))
    have g := ha.frame
    refine WP.mono (WP.keep [.x9] (Q := fun u => u.mem = t.mem) (by brun [exec_addImm_w]) (by decide) (by decide)
      (by decide +kernel)) fun u ⟨hm, k⟩ => ?_
    exact (g.keep k hm).hdr (by simp [GenPublic.headers]) (by decide)
  refine two_post hct fun q t ⟨o, st, s, ha, hl, _, haf⟩ =>
    WP.mono (after_head ⟨hl, [], rfl⟩ haf) fun u ⟨hx9, hx10, hm⟩ =>
      ⟨⟨o, st, ha, hm⟩, by rw [hx9, ha.status], by rw [hx10, ha.cand]⟩

/-! ## A generation exhausted -/

/-- The generations' test, at the point. -/
def LeftCT (q : GenPoint) (u : State) : Prop :=
  ∃ original used st, GenFrame q.inputs original used st u ∧ u.gpr .x8 = q.inputs.stp ∧
    u.gpr .x10 = BitVec.ofNat 64 q.left ∧ q.left = st.left ∧
    isa.eval (.zero .x .x12) u = some (decide (q.left < 2))

theorem LeftCT.any {q : GenPoint} {u : State} (h : LeftCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, g, _⟩ := h; ⟨o, _, _, g⟩

theorem LeftCT.eval {q : GenPoint} {u : State} (h : LeftCT q u) :
    isa.eval (.zero .x .x12) u = some (decide (q.left < 2)) :=
  let ⟨_, _, _, _, _, _, _, e⟩ := h; e

/-- One generation fewer, then the state's pointer reloaded. -/
theorem dec_hdr (q : GenPoint) (s : State) (h : LeftCT q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [.subImm .x .x10 .x10 1, VG.Impl.Bignum.AArch64.st .x10 .x8 40]) s (Hdr7 q.inputs) := by
  obtain ⟨⟨o, u, st, g, h8, h10, -, -⟩, -⟩ := h
  have scr := g.scr
  have sst := g.stateScr
  have hs5 : InRegions s.wr (q.inputs.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  have hnF : q.inputs.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hnS : q.inputs.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hk7 (v : BitVec 64) :
      (s.mem.writeW (q.inputs.stp + BitVec.ofNat 64 40) v).readW (q.inputs.F + BitVec.ofNat 64 (8 * 7)) 64 =
        q.inputs.stp :=
    ((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨q.inputs.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := q.inputs.frame)
      (Offset.contains_base _ (by decide) (by omega)) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact g.input.frame_state) (by decide)).trans
      (g.headers (7, q.inputs.stp) (by simp [GenPublic.headers]))
  have hl7 := g.frame_ld (8 * 7) (by decide)
  brun [VG.Impl.Bignum.AArch64.st, h8, h10, hs5]
  exact ⟨by simp only [RegUpd.gpr_write_of_ne _ _ _ (show Reg.x19 ≠ .x10 by decide)]; exact g.x19, hl7, hk7 _⟩

theorem exhausted_ct : RelCT isa (Two MidCT) exhaustedGen (fun _ _ => True) := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (Ψ := LeftCT) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp)
    [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.any.x19) (fun _ _ h => h.any.stp) (by taint_decide)
    (by taint_decide)) fun q u ⟨o, st, ha, hm⟩ => WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hx8, hx10, hmem⟩, k⟩ =>
      ⟨o, _, _, hm.frame.keep k hmem, hx8, by rw [hx10, ha.1], ha.1.symm, by
        rw [eval_zero, hb, ← ha.1]; by_cases h2 : 2 ≤ st.left <;> simp [h2]; omega⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.eval.trans h₂.eval.symm) ?_ ?_
  · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.any) (by decide)
  · refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => Hdr7 q.inputs t) [.x19, .x8] ?_
      (by taint_decide) dec_hdr) (nextPrime_ct (fun q : GenPoint => q.inputs) (fun _ _ h => h) (phase := 0) (by decide)))
    rintro q s t ⟨⟨o₁, _, _, g₁, a₁, -⟩, -⟩ ⟨⟨o₂, _, _, g₂, a₂, -⟩, -⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [g₁.x19.trans g₂.x19.symm, a₁.trans a₂.symm]

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ ((v.gpr .x0).setWidth 32).toNat = q.key ∧ q.key < 3

theorem keyStatus_lt3 (k : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus k < 3 := by
  unfold keyStatus; split <;> decide

/-- The key's first test, at the point. -/
def Key1CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ v.gpr .x9 = BitVec.ofNat 64 q.key ∧ q.key < 3 ∧
    isa.eval (.zero .x .x12) v = some (decide (q.key = 1))

/-- The key's second test, at the point. -/
def Key2CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ isa.eval (.zero .x .x12) v = some (decide (q.key = 2))

theorem after_key_ct : RelCT isa (Two AfterKCT) afterKey (fun _ _ => True) := by
  unfold afterKey
  refine RelCT.seq (two_post (Ψ := Key1CT) (two_taint [] (no_pins _) (by taint_decide))
    fun q v ⟨⟨o, u, st, g⟩, hs, h3⟩ => WP.mono (keyStatus_guard hs) fun w ⟨⟨hx9, he, hmem⟩, k⟩ =>
      ⟨⟨o, u, st, g.keep k hmem⟩, hx9, h3, he⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact finishWith_ct (fun q => q.inputs) (fun _ _ h => h.1.1.stp) (by decide)
  · refine RelCT.seq (two_post (Ψ := Key2CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q v ⟨⟨⟨o, u, st, g⟩, hx9, h3, _⟩, _⟩ => WP.mono (sub_guard (k := 2) (by decide) hx9 (by omega))
        fun w ⟨⟨he, hmem⟩, k⟩ => ⟨⟨o, u, st, g.keep k hmem⟩, he⟩) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact nextPrime_ct (fun q => q.inputs) (fun _ _ h => h.1.1.stp) (by decide)
    · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.1) (by decide)

/-! ## A prime accepted -/

/-- The phase's test, at the point, after an accepted prime. -/
def PhCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 ∧ u.gpr .x10 = BitVec.ofNat 64 q.ph

theorem accepted_ct [Key.KeyProof] :
    RelCT isa (Two fun q u => MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0) (accepted keyCall) (fun _ _ => True) := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := PhCT) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp)
    [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.1.any.x19) (fun _ _ h => h.1.any.stp) (by taint_decide)
    (by taint_decide))
    fun q u ⟨⟨o, st, ha, hm⟩, h1, h0⟩ => WP.mono (phase_ok hm.frame) fun v ⟨⟨hx10, hmem⟩, k⟩ =>
      ⟨⟨o, st, ha, hm.keep k hmem⟩, h1, h0, by rw [hx10, ha.2.1]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2, h₂.2.2.2]) ?_ ?_
  · exact nextPrime_ct (fun q => q.inputs) (fun _ _ h => h.1.1.any.stp) (by decide)
  · -- `q`: the key.
    have hk : ∀ q u, (PhCT q u ∧ isa.eval (.zero .x .x10) u = some false) → KeyCT q u := by
      rintro q u ⟨⟨⟨o, st, ha, hm⟩, h1, h0, hx⟩, hf⟩
      have hph : q.ph ≠ 0 := by
        intro h0'
        rw [eval_zero, hx, h0'] at hf
        cases hf
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact absurd (ha.2.1.symm.trans rfl) hph
      | q pB =>
        cases ho : (rOf q.inputs o q.used ⟨left, .q pB, remaining⟩).outcome with
        | entropy k a => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | exhausted => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | accepted c => exact ⟨o, _, _, c, pB, ha, hm, ho, by rw [ha.cand]; omega, rfl⟩
    refine RelCT.seq (two_post (Ψ := AfterKCT) ((key_run_ct).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ =>
      ⟨q, hk q _ h₁, hk q _ h₂, hsp⟩) fun _ _ h => h) fun q u h => ?_) after_key_ct
    have hkc := hk q u h
    obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := hkc
    refine WP.mono (key_run hm.frame) fun v hak => ⟨⟨o, _, _, hak.frame⟩, ?_, ?_⟩
    · rw [hak.status, (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
    · rw [← (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
      exact keyStatus_lt3 _

/-! ## The classification -/

/-- The test of the search's status 3, at the point. -/
def Mid3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .x10 = BitVec.ofNat 64 q.cand ∧ q.status ≠ 0 ∧
    isa.eval (.zero .x .x12) u = some (decide (q.status = 3))

theorem accepted_of {q : GenPoint} {u : State}
    (h : (Mid3CT q u ∧ isa.eval (.zero .x .x12) u = some false) ∧ isa.eval (.zero .x .x10) u = some false) :
    MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 := by
  obtain ⟨⟨⟨hm, hx10, h0, he⟩, hf3⟩, hf4⟩ := h
  have hs := MidCT.status hm
  have h3 : q.status ≠ 3 := ev_false he hf3
  have hu64 : q.cand < 2 ^ 64 := by
    obtain ⟨o, st, ha, hm'⟩ := hm
    have := hm'.frame.used_le; have := hm'.frame.input.cfacts.rand64; rw [← ha.cand]; omega
  refine ⟨hm, by omega, fun hc => ?_⟩
  rw [eval_zero, hx10, ofNat_beq_zero hu64, hc] at hf4
  cases hf4

theorem classify_ct [Key.KeyProof] : RelCT isa (Two AfterCT) (classify keyCall) (fun _ _ => True) := by
  unfold classify
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq head_ct ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.1, h₂.2.1]) ?_ ?_
  · exact frame_ct (fun q => q.inputs) (fun _ _ h => h.1.1.any.x19) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Mid3CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q u ⟨⟨hm, hx9, hx10⟩, hf⟩ => ?_) ?_
    · have hs := MidCT.status hm
      have h0 : q.status ≠ 0 := by
        intro h0'; rw [eval_zero, hx9, h0'] at hf; cases hf
      refine WP.mono (sub_guard (k := 3) (by decide) hx9 (by omega)) fun v ⟨⟨he3, hmem⟩, k⟩ =>
        ⟨let ⟨o, st, ha, hm'⟩ := hm; ⟨o, st, ha, hm'.keep k hmem⟩, by rw [k.gpr _ (by decide)]; exact hx10, h0, he3⟩
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
    · exact (exhausted_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h)
    · refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1, h₂.1.2.1]) ?_ ?_
      · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.1.1.any) (by decide)
      · exact (accepted_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, accepted_of h₁, accepted_of h₂, hsp⟩)
          fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64.Generate
