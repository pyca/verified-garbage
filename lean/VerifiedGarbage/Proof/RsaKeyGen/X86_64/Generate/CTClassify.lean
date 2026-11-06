module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTCalls
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTCalls
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # The classification's timing

After the search, each test the controller branches on is of the point:
the search's status and consumption, the generations left, the phase and
the key's status. Every block between them the taint analysis checks from
the frame's public words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (candidate_status_guard second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem ev_false {c : Cond} {s : State} {b : Prop} [Decidable b] (he : eval c s = some (decide b))
    (hf : isa.eval c s = some false) : ¬b := fun h => by
  have hx : some (decide b) = some false := he.symm.trans hf
  simp [h] at hx

theorem no_pins {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

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

/-! ## The blocks between the tests -/

theorem frame_ct {Φ : GenPoint → State → Prop} {c : Prog isa} (hΦ : ∀ q s, Φ q s → AnyFrame q.inputs s)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (genT []) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  frame_taint (fun q => q.inputs) [] hΦ (no_pins Φ) h

/-! ## The head -/

/-- The head's test, at the point. -/
def HeadCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .rax = BitVec.ofNat 64 q.status ∧ u.gpr .rcx = BitVec.ofNat 64 q.cand ∧
    eval .e u = some (decide (q.status = 0))

theorem head_ct : RelCT isa (Two AfterCT) (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)),
    .mov .rcx (.mem { base := .rcx }), .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx),
    .store (field 8) .rdx, .alu .test .rax (.reg .rax)]) (Two HeadCT) :=
  two_post (frame_ct (fun _ _ ⟨o, _, _, _, _, _, ha⟩ => ⟨o, _, _, ha.frame⟩) (by taint_decide))
    fun q t ⟨o, st, s, ha, hl, _, haf⟩ => WP.mono (after_head ⟨hl, [], rfl⟩ haf) fun u ⟨he, hax, hcx, hm⟩ =>
      ⟨⟨o, st, ha, hm⟩, by rw [hax, ha.status], by rw [hcx, ha.cand], by rw [he, ha.status]⟩

/-! ## A generation exhausted -/

/-- The generations' test, at the point. -/
def LeftCT (q : GenPoint) (u : State) : Prop :=
  AnyFrame q.inputs u ∧ u.gpr .rax = q.inputs.stp ∧ u.gpr .rcx = BitVec.ofNat 64 q.left ∧
    eval .b u = some (decide (q.left < 2))

theorem exhausted_ct : RelCT isa (Two MidCT) exhaustedGen (fun _ _ => True) := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (Ψ := LeftCT) (frame_ct (fun _ _ h => h.any) (by taint_decide))
    fun q u ⟨o, st, ha, hm⟩ => WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hax, hcx, hmem⟩, k⟩ =>
      ⟨⟨o, _, _, hm.frame.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, hax,
        by rw [hcx]; exact congrArg _ ha.1,
        by rw [hb]; congr 2; exact propext ⟨fun h => ha.1 ▸ h, fun h => ha.1.symm ▸ h⟩⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
  · exact frame_taint (fun q => q.inputs) [.rax, .rcx] (fun _ _ h => h.1.1)
      (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [h₁.1.2.1.trans h₂.1.2.1.symm, h₁.1.2.2.1.trans h₂.1.2.2.1.symm]) (by taint_decide)

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ ((v.gpr .rax).setWidth 32).toNat = q.key ∧ q.key < 3

theorem keyStatus_lt3 (k : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus k < 3 := by
  unfold keyStatus; split <;> decide

/-- The key's first test, at the point. -/
def Key1CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ v.gpr .rax = BitVec.ofNat 64 q.key ∧ q.key < 3 ∧ eval .e v = some (decide (q.key = 1))

/-- The key's second test, at the point. -/
def Key2CT (q : GenPoint) (v : State) : Prop := AnyFrame q.inputs v ∧ eval .e v = some (decide (q.key = 2))

theorem after_key_ct : RelCT isa (Two AfterKCT) afterKey (fun _ _ => True) := by
  unfold afterKey
  refine RelCT.seq (two_post (Ψ := Key1CT) (frame_ct (fun _ _ h => h.1) (by taint_decide))
    fun q v ⟨⟨o, u, st, g⟩, hs, h3⟩ => WP.mono (candidate_status_guard v) fun w ⟨⟨he, hax, hmem⟩, k⟩ =>
      ⟨⟨o, u, st, g.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩,
        status_of hs hax, h3, by rw [he, hs]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Key2CT) (frame_ct (fun _ _ h => h.1.1) (by taint_decide))
      fun q v ⟨⟨⟨o, u, st, g⟩, hax, h3, _⟩, _⟩ => WP.mono (second_status_guard hax (by omega))
        fun w ⟨⟨he, hmem⟩, k⟩ =>
        ⟨⟨o, u, st, g.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, he⟩) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
    · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)

/-! ## A prime accepted -/

/-- The phase's test, at the point, after an accepted prime. -/
def PhCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 ∧ eval .e u = some (decide (q.ph = 0))

theorem accepted_ct [Key.KeyProof] : RelCT isa (Two fun q u => MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0) (accepted keyCall)
    (fun _ _ => True) := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := PhCT) (frame_ct (fun _ _ h => h.1.any) (by taint_decide))
    fun q u ⟨⟨o, st, ha, hm⟩, h1, h0⟩ => WP.mono (phase_ok hm.frame) fun v ⟨⟨he, hmem⟩, k⟩ =>
      ⟨⟨o, st, ha, hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, h1, h0,
        by rw [he]; show some (decide (phaseWord st.phase = 0)) = _; rw [ha.2.1]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
  · -- `q`: the key.
    have hk : ∀ q u, (PhCT q u ∧ eval .e u = some false) → KeyCT q u := by
      rintro q u ⟨⟨⟨o, st, ha, hm⟩, h1, h0, he⟩, hf⟩
      have hph : q.ph ≠ 0 := ev_false he hf
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact absurd (ha.2.1.symm.trans rfl) hph
      | q pB =>
        cases ho : (rOf q.inputs o q.used ⟨left, .q pB, remaining⟩).outcome with
        | entropy k a => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | exhausted => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | accepted c => exact ⟨o, _, _, c, pB, ha, hm, ho, by rw [ha.cand]; omega, rfl⟩
    refine RelCT.seq (two_post (Ψ := AfterKCT) ((key_run_ct).mono (fun _ _ ⟨q, h₁, h₂⟩ =>
      ⟨q, hk q _ h₁, hk q _ h₂⟩) fun _ _ h => h) fun q u h => ?_) after_key_ct
    have hkc := hk q u h
    obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := hkc
    refine WP.mono (key_run hm.frame) fun v hak => ⟨⟨o, _, _, hak.frame⟩, ?_, ?_⟩
    · rw [hak.status, (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
    · rw [← (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
      exact keyStatus_lt3 _

/-! ## The classification -/

/-- The test of the search's status 3, at the point. -/
def Mid3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .rcx = BitVec.ofNat 64 q.cand ∧ q.status ≠ 0 ∧ eval .e u = some (decide (q.status = 3))

/-- The test of the octets the search consumed, at the point. -/
def Mid4CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ eval .e u = some (decide (q.cand = 0))

theorem classify_ct [Key.KeyProof] : RelCT isa (Two AfterCT) (classify keyCall) (fun _ _ => True) := by
  unfold classify
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq head_ct ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Mid3CT) (frame_ct (fun _ _ h => h.1.1.any) (by taint_decide))
      fun q u ⟨⟨⟨o, st, ha, hm⟩, hax, hcx, he⟩, hf⟩ => ?_) ?_
    · have hs := MidCT.status ⟨o, st, ha, hm⟩
      have h0 : q.status ≠ 0 := ev_false he hf
      refine WP.mono (cmp3_guard hax (by omega)) fun v ⟨⟨he3, hmem⟩, k⟩ =>
        ⟨⟨o, st, ha, hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩,
          by rw [k.gpr (by decide)]; exact hcx, h0, he3⟩
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
    · exact (exhausted_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1.1, h₂.1.1⟩) fun _ _ h => h)
    · refine RelCT.seq (two_post (Ψ := Mid4CT) (frame_ct (fun _ _ h => h.1.1.any) (by taint_decide))
        fun q u ⟨⟨hm, hcx, h0, he⟩, hf⟩ => ?_) ?_
      · have hs := MidCT.status hm
        have h3 : q.status ≠ 3 := ev_false he hf
        obtain ⟨o, st, ha, hm'⟩ := hm
        have hu64 : q.cand < 2 ^ 64 := by
          have := hm'.frame.used_le; have := hm'.frame.input.cfacts.rand64; rw [← ha.cand]; omega
        refine WP.mono (test_guard hcx hu64) fun v ⟨⟨he4, hmem⟩, k⟩ =>
          ⟨⟨o, st, ha, hm'.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, by omega, he4⟩
      refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
      · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
      · refine (accepted_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, ?_, ?_⟩) fun _ _ h => h)
        · obtain ⟨⟨hm, h1, he⟩, hf⟩ := h₁
          exact ⟨hm, h1, ev_false he hf⟩
        · obtain ⟨⟨hm, h1, he⟩, hf⟩ := h₂
          exact ⟨hm, h1, ev_false he hf⟩

end VG.Proof.RsaKeyGen.X86_64.Generate
