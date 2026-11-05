module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTCall
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTCall
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # An iteration of the search is constant time (ARMv7)

Each branch is on the point's public values, or on the candidate's status
and consumption, which the trace gives (`status_eq`, `used_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- Code that touches no memory leaks nothing, from any states. -/
theorem quiet_ct {P : State → State → Prop} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (h : (taint.check (Taint.ofRegs []) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ h => nomatch h) h

/-! ## After the candidate -/

/-- The candidate's status and consumption in `r0` and `r12`, and the
first comparison. -/
def RegsCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  AfterCT p T q t ∧ t.gpr .r0 = BitVec.ofNat 32 (pubStatus T q.2.2) ∧
    t.gpr .r12 = BitVec.ofNat 32 (pubUsed p T q.2.2)

def HeadCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  RegsCT p T q t ∧ isa.eval .eq t = some (decide (pubStatus T q.2.2 = 1))

theorem AfterCT.keep {p : SearchPublic} {T : List Nat} {q : Pt} {s t : State} (h : AfterCT p T q s)
    {ws : List Reg} (k : Rest ws s t) (hm : t.mem = s.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r11], r ∉ ws := by decide) (h0 : t.gpr .r0 = s.gpr .r0) :
    AfterCT p T q t := by
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  refine ⟨o, hT, hl.keep k hm hws, hf, hk, hr, ?_⟩
  obtain ⟨p0, p1, p2⟩ := hp
  exact ⟨by rw [h0]; exact p0, by rw [hm]; exact p1, by rw [hm]; exact p2⟩

theorem after_r0 {p : SearchPublic} {T : List Nat} {q : Pt} {t : State} (h : AfterCT p T q t) :
    t.gpr .r0 = BitVec.ofNat 32 (pubStatus T q.2.2) := by
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  rw [status_ofNat hp.1, ← status_eq hT hf hk]; rfl

theorem head_ready (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) (h : AfterCT p T q t) :
    WP isa (.block [.ldr .r12 .r6 0, .cmp .r0 (.imm 1)]) t (HeadCT p T q) := by
  have h0 := after_r0 h
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  have hw : Spec.Rsa.wordsAt t.mem (State.addr p.up) 1 = [BitVec.ofNat 64 (candUsed p o q.1)] := hp.2.2
  rw [used_eq hl.input hT hf hk] at hw
  have st : pubStatus T q.2.2 < 4 := by
    rw [← status_eq hT hf hk]; unfold candStatus Spec.RsaKeyGen.candidateStatus; split <;> decide
  refine WP.mono (head_ok hl hw st h0) fun u ⟨⟨h12, he, hm⟩, k⟩ => ⟨⟨?_, ?_, h12⟩, he⟩
  · exact AfterCT.keep ⟨o, hT, hl, hf, hk, hr, hp⟩ k hm (h0 := k.gpr .r0 (by decide))
  · rw [k.gpr .r0 (by decide), h0]

theorem after_pins (p : SearchPublic) (T : List Nat) : Pins (AfterCT p T) [.r0, .r6] := by
  intro q s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (after_r0 h₁).trans (after_r0 h₂).symm
  · obtain ⟨_, _, l₁, _⟩ := h₁; obtain ⟨_, _, l₂, _⟩ := h₂; exact l₁.r6.trans l₂.r6.symm

/-- After the second comparison. -/
def Head2CT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  RegsCT p T q t ∧ isa.eval .eq t = some (decide (pubStatus T q.2.2 = 0))

theorem head2_ready (p : SearchPublic) (T : List Nat) (q : Pt) (t : State)
    (h : HeadCT p T q t ∧ isa.eval .eq t = some false) :
    WP isa (.block [.cmp .r0 (.imm 0)]) t (Head2CT p T q) := by
  obtain ⟨⟨⟨ha, h0, h12⟩, -⟩, -⟩ := h
  have st : pubStatus T q.2.2 < 2 ^ 32 := by
    obtain ⟨o, hT, hl, hf, hk, -⟩ := ha
    rw [← status_eq hT hf hk]; unfold candStatus Spec.RsaKeyGen.candidateStatus; split <;> decide
  refine WP.mono (cmp0_ok h0 st) fun u ⟨⟨he, hm⟩, k⟩ => ⟨⟨?_, ?_, ?_⟩, he⟩
  · exact AfterCT.keep ha k hm (h0 := k.gpr .r0 (by decide))
  · rw [k.gpr .r0 (by decide), h0]
  · rw [k.gpr .r12 (by decide), h12]

theorem regs_pins (p : SearchPublic) (T : List Nat) : Pins (RegsCT p T) [.r0, .r4, .r5, .r8, .r9, .r12] := by
  intro q s₁ s₂ ⟨a₁, z₁, w₁⟩ ⟨a₂, z₂, w₂⟩ r hr
  obtain ⟨_, _, l₁, _⟩ := a₁
  obtain ⟨_, _, l₂, _⟩ := a₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [z₁.trans z₂.symm, l₁.r4.trans l₂.r4.symm, l₁.r5.trans l₂.r5.symm, l₁.r8.trans l₂.r8.symm,
    l₁.r9.trans l₂.r9.symm, w₁.trans w₂.symm]

theorem classify_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AfterCT p T)) Impl.RsaKeyGen.Arm.Search.classify (fun _ _ => True) := by
  unfold Impl.RsaKeyGen.Arm.Search.classify
  refine RelCT.seq (two_piece [.r0, .r6] (after_pins p T) (by taint_decide) (head_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) (accept_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide) (head2_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · refine two_map (fun q => q.1) (fun q s h => ?_) (short_ct p)
    rcases h with ⟨⟨⟨⟨o, -, hl, -⟩, -, -⟩, -⟩, -⟩
    exact ⟨o, hl.toSearchBase, hl.r8⟩
  · exact two_taint _ (fun q s₁ s₂ h₁ h₂ => regs_pins p T q s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)

/-! ## A candidate, or a short tape -/

/-- A loop state with candidates left. -/
def Live0 (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop := LiveCT p T q s ∧ q.2.1 ≠ 0

def Live0' (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  Live0 p T q s ∧ s.gpr .r0 = BitVec.ofNat 32 p.randLen

def GuardCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  Live0 p T q s ∧ isa.eval .eq s = some (decide (p.randLen - q.1 < p.len))

theorem guard_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : Live0 p T q s) :
    WP isa (.block [arg .r0 0 4]) s (Live0' p T q) := by
  obtain ⟨⟨o, hT, hl, hf⟩, hk⟩ := h
  refine WP.mono (withRest_all [.r0] (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 p.randLen ∧ t.mem = s.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h0, hm⟩, k⟩ => ⟨⟨⟨o, hT, hl.keep k hm, hf⟩, hk⟩, h0⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hl.arg_addr 4, hl.arg_read (j := 4) (by decide), hl.arg_value (j := 4) (by decide), randLen_arg hl.input, c]

theorem guard_ready (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : Live0 p T q s) :
    WP isa (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5), .mov .r12 (.imm 0),
      .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]) s (GuardCT p T q) := by
  obtain ⟨⟨o, hT, hl, hf⟩, hk⟩ := h
  have hi := hl.input
  have f := hi.facts
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  have rl := f.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  have hu := hl.used_le
  refine WP.mono (withRest_all [.r0, .r12]
    (Q := fun t => isa.eval .eq t = some (decide (p.randLen - q.1 < p.len)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨⟨o, hT, hl.keep k hm, hf⟩, hk⟩, he⟩
  unfold arg
  have c4 : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hl.arg_addr 4, hl.arg_read (j := 4) (by decide), hl.arg_value (j := 4) (by decide), randLen_arg hi,
    hl.r8, hl.r5, BitVec.ofNat_sub_ofNat_of_le _ _ (show q.1 < 2 ^ 32 by omega) hu, c4,
    toNat_small (n := p.len) (by omega), toNat_small (n := p.randLen - q.1) (by omega)]
  exact carry_eval (P := p.randLen - q.1 < p.len) (not_decide_le _ _)

theorem live0'_pins (p : SearchPublic) (T : List Nat) : Pins (Live0' p T) [.r0, .r5, .r8] := by
  intro q s₁ s₂ ⟨⟨⟨_, _, l₁, _⟩, _⟩, z₁⟩ ⟨⟨⟨_, _, l₂, _⟩, _⟩, z₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [z₁.trans z₂.symm, l₁.r5.trans l₂.r5.symm, l₁.r8.trans l₂.r8.symm]

theorem live_pins45 {p : SearchPublic} {T : List Nat} {Φ : Pt → State → Prop} (h : ∀ q s, Φ q s → LiveCT p T q s) :
    Pins Φ [.r4, .r5] := fun q s₁ s₂ h₁ h₂ r hr =>
  live_pins p T q s₁ s₂ (h q s₁ h₁) (h q s₂ h₂) r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp)

theorem candidateStep_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (Live0 p T)) (candidateStep c.call) (fun _ _ => True) := by
  unfold candidateStep
  have gt : RelCT isa (Two (Live0 p T)) (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]) (fun _ _ => True) := by
    change RelCT isa _ (.block ([arg .r0 0 4] ++ [.dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)])) _
    exact RelCT.block_append (RelCT.seq (ldrSp_ct (guard_load p T)) (two_taint _ (live0'_pins p T) (by taint_decide)))
  refine RelCT.seq (two_post gt (guard_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun q t => ShortCT p q.1 t)
      (zeroOut_ct (live_pins45 fun q s h => h.1.1.1)) fun q s h => ?_) (two_map (fun q => q.1) (fun _ _ h => h) (short_ct p))
    obtain ⟨⟨⟨⟨o, _, hl, _⟩, _⟩, _⟩, _⟩ := h
    exact WP.mono (zeroOut_ok hl.toSearchBase) fun t ⟨⟨_, hf⟩, k⟩ =>
      ⟨o, hl.toSearchBase.step k (by decide) hf (out_changes hl.input) (out_apart hl.input),
        (k.gpr .r8 (by decide)).trans hl.r8⟩
  · refine RelCT.seq ((candidateRun_ct c p T).mono (fun s₁ s₂ ⟨q, h₁, h₂, sp⟩ => ⟨q, ?_, ?_, sp⟩) fun _ _ h => h)
      (classify_ct p T)
    · rcases h₁ with ⟨⟨⟨lv, hk⟩, eg⟩, ef⟩
      refine ⟨lv, hk, ?_⟩
      obtain ⟨o, -, hl, -⟩ := lv
      have := hl.used_le
      rw [eg] at ef
      have := of_decide_eq_false (Option.some.inj ef)
      omega
    · rcases h₂ with ⟨⟨⟨lv, hk⟩, eg⟩, ef⟩
      refine ⟨lv, hk, ?_⟩
      obtain ⟨o, -, hl, -⟩ := lv
      have := hl.used_le
      rw [eg] at ef
      have := of_decide_eq_false (Option.some.inj ef)
      omega

end VG.Proof.RsaKeyGen.Arm.Search
