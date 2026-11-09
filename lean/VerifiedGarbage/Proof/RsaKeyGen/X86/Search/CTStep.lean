module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTCall
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Taint

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # Two runs of an iteration (i686)

After the candidate, its status and the octets it consumed are public, from
the trace (`status_eq`, `used_eq`): the classification branches on them,
and reads `used` at its public pointer (`classify_ct`). Whether the tape
holds a candidate, and whether counted candidates are left, are public
(`candidateStep_ct`, `iteration_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeEntropy)

theorem candStatus_lt (p : SearchPublic) (o : State) (used : Nat) : candStatus p o used < 4 := by
  unfold candStatus
  cases candOp p o used with
  | none => simp [Spec.RsaKeyGen.candidateStatus]
  | some x => obtain ⟨c, r⟩ := x; cases c <;> simp [Spec.RsaKeyGen.candidateStatus]

/-- `mov edx, [used]`'s pointer. -/
theorem upLoad_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block [.mov .edx (.mem (param 0 2))]) s fun u => u.gpr .edx = p.up ∧ u.mem = s.mem := by
  have hup : p.up = arg o 2 := by rw [← hb.input.2]; rfl
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 2) (d := 28) rfl, hb.arg_in (i := 2) (by decide),
    hb.arg_val (i := 2) (by decide), hup]

/-- After the candidate, at the loop point `q`. -/
def ClsCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧
    CandPost p (searchP o) (searchRand o) q.1 s ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen

/-- After the classification's head: the status in `eax`, the octets
consumed in `ecx`, both public. -/
def AfterHead (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  (∃ o, SearchBase p o t) ∧ t.gpr .esi = BitVec.ofNat 32 q.1 ∧ q.1 ≤ p.randLen ∧
    t.gpr .eax = BitVec.ofNat 32 (pubStatus T q.2.2) ∧ t.gpr .ecx = BitVec.ofNat 32 (pubUsed p T q.2.2) ∧
    pubStatus T q.2.2 < 4 ∧ pubUsed p T q.2.2 < 2 ^ 32

theorem afterHead_pins (p : SearchPublic) (T : List Nat) : Pins (AfterHead p T) [.esp, .esi, .eax, .ecx] := by
  rintro q s₁ s₂ ⟨⟨_, h₁⟩, i₁, _, a₁, c₁, _⟩ ⟨⟨_, h₂⟩, i₂, _, a₂, c₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.sp.trans h₂.sp.symm, i₁.trans i₂.symm, a₁.trans a₂.symm, c₁.trans c₂.symm]

theorem afterHead_cmp {p : SearchPublic} {T : List Nat} {q : Pt} {t : State} (h : AfterHead p T q t)
    {r : Reg} {n : Nat} (hr : t.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) (hrs : r = .eax ∨ r = .ecx) :
    WP isa (.block [.alu .cmp r (.imm 0)]) t fun u => AfterHead p T q u ∧ u.zf = some (decide (n = 0)) := by
  obtain ⟨⟨o, hb⟩, hi, hu, ha, hc, hs, hn'⟩ := h
  refine WP.mono (cmp0_ok hr hn) fun u ⟨⟨hz, hr', hm⟩, ku, sy⟩ => ⟨⟨⟨o, hb.step ku (by rcases hrs with rfl | rfl <;> decide) sy hm⟩,
    ?_, hu, ?_, ?_, hs, hn'⟩, hz⟩
  · exact (ku.gpr (by rcases hrs with rfl | rfl <;> decide)).trans hi
  · rcases hrs with rfl | rfl
    · exact hr'.trans ha
    · exact (ku.gpr (by decide)).trans ha
  · rcases hrs with rfl | rfl
    · exact (ku.gpr (by decide)).trans hc
    · exact hr'.trans hc

theorem reject_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two fun q t => AfterHead p T q t ∧ isa.eval .e t = some false) reject fun _ _ => True := by
  unfold reject
  refine RelCT.seq (two_piece (Ψ := fun q t => AfterHead p T q t ∧ t.zf = some (decide (pubUsed p T q.2.2 = 0)))
    [.esp, .esi, .eax, .ecx] (fun q s₁ s₂ h₁ h₂ => afterHead_pins p T q s₁ s₂ h₁.1 h₂.1) (by taint_decide)
    fun q t h => afterHead_cmp h.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.2 (.inr rfl)) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map id (fun q t h => h.1.1.1) (exhausted_ct (fun (_ : Pt) => p))
  · exact two_taint [.eax] (fun q s₁ s₂ h₁ h₂ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact h₁.1.1.2.2.2.1.trans h₂.1.1.2.2.2.1.symm) (by taint_decide)

/-- The classification's head, `mov edx, [used]`, then `mov ecx, [edx]; cmp eax, 1`. -/
def HeadCT (p : SearchPublic) (T : List Nat) (q : Pt) (u : State) : Prop :=
  u.gpr .edx = p.up ∧ (∃ o, SearchBase p o u) ∧ u.gpr .eax = BitVec.ofNat 32 (pubStatus T q.2.2) ∧
    WP isa (.block [.mov .ecx (.mem (at_ .edx 0)), .alu .cmp .eax (.imm 1)]) u fun t =>
      AfterHead p T q t ∧ t.zf = some (decide (pubStatus T q.2.2 = 1))

theorem classify_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (ClsCT p T)) classify fun _ _ => True := by
  unfold classify
  refine RelCT.seq_block_append (l₁ := ([.mov .edx (.mem (param 0 2))] : List Instr)) (RelCT.seq (two_piece (Φ := ClsCT p T) (Ψ := HeadCT p T)
    [.esp] (fun q s₁ s₂ ⟨_, _, L₁, _⟩ ⟨_, _, L₂, _⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact L₁.sp.trans L₂.sp.symm) (by taint_decide)
    fun q s ⟨o, hT, L, hf, cp, hk, hr⟩ => ?_) ?_)
  · have est := status_eq hT hf hk
    have eu := used_eq L.input hT hf hk
    have h0 : s.gpr .eax = BitVec.ofNat 32 (candStatus p o q.1) := status_ofNat cp.1
    have H := head_ok L (n := candUsed p o q.1) cp.2.2 (candStatus_lt p o q.1) h0
    rw [show ([.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .cmp .eax (.imm 1)] : List Instr) =
      [.mov .edx (.mem (param 0 2))] ++ [.mov .ecx (.mem (at_ .edx 0)), .alu .cmp .eax (.imm 1)] from rfl,
      WP.block_append_iff] at H
    have bu := candUsed_le L.input L.used_le
    have rl := L.input.facts.randLen
    have lv := L.input.len_valid
    unfold primeEntropy at rl
    refine WP.mono (WP.block_and H (WP.blockKeep [.edx] (upLoad_ok L.toSearchBase) (by rfl)))
      fun u ⟨hc, ⟨he, hm⟩, ku, syu⟩ => ⟨he, ⟨o, L.toSearchBase.step ku (by decide) syu hm⟩, ?_, ?_⟩
    · rw [ku.gpr (by decide), h0, est]
    · refine WP.mono hc fun t ⟨⟨hc', ha', hz', hm'⟩, kt, syt⟩ => ⟨⟨⟨o, L.toSearchBase.step kt (by decide) syt hm'⟩,
        (kt.gpr (by decide)).trans L.esi, L.used_le, by rw [ha', est], by rw [hc', eu], est ▸ candStatus_lt p o q.1,
        by rw [← eu]; omega⟩, by rw [hz', est]⟩
  refine RelCT.seq (two_piece (Φ := HeadCT p T)
    (Ψ := fun q t => AfterHead p T q t ∧ t.zf = some (decide (pubStatus T q.2.2 = 1))) [.edx, .eax, .esp]
    (fun q s₁ s₂ ⟨d₁, ⟨_, b₁⟩, a₁, _⟩ ⟨d₂, ⟨_, b₂⟩, a₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [d₁.trans d₂.symm, a₁.trans a₂.symm, b₁.sp.trans b₂.sp.symm]) (by taint_decide)
    fun q u h => h.2.2.2) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) accept_ct ?_
  refine RelCT.seq (two_piece (Ψ := fun q t => AfterHead p T q t ∧ t.zf = some (decide (pubStatus T q.2.2 = 0)))
    [.esp, .esi, .eax, .ecx] (fun q s₁ s₂ h₁ h₂ => afterHead_pins p T q s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)
    fun q t h => afterHead_cmp h.1.1 h.1.1.2.2.2.1 (by have := h.1.1.2.2.2.2.2.1; omega) (.inl rfl)) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ (two_map id (fun q t h => ⟨h.1.1, h.2⟩) (reject_ct p T))
  exact two_map (fun q => q.1) (fun q t h => let ⟨⟨o, hb⟩, hi, hu, _⟩ := h.1.1; ⟨o, hb, hi, hu⟩) (short_ct p)

/-- The candidate step's comparison: the tape left with `out_len`. -/
theorem stepHead_ok {p : SearchPublic} {o s : State} {used k : Nat} (hl : SearchLive p o used k s) :
    WP isa (.block [.mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi), .alu .cmp .eax (.mem (param 0 1))]) s
      fun t => SearchLive p o used k t ∧ t.cf = some (decide (p.randLen - used < p.len)) := by
  have hi := hl.input
  have f := hi.facts
  have hv := hi.len_valid
  have rl := f.randLen
  unfold primeEntropy at rl
  have hu := hl.used_le
  have hb := hl.toSearchBase
  refine WP.mono (WP.blockKeep (is := [.mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi),
      .alu .cmp .eax (.mem (param 0 1))]) [.eax]
    (Q := fun t => t.cf = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun u ⟨⟨he, hm⟩, ku, sy⟩ => ⟨hl.keep ku sy hm, he⟩
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 8) (d := 52) rfl, hb.arg_ea (i := 1) (d := 24) rfl,
    hb.arg_in (i := 8) (by decide), hb.arg_in (i := 1) (by decide), hb.arg_val (i := 8) (by decide),
    hb.arg_val (i := 1) (by decide), hi.randLen_arg, hi.len_arg, hl.esi,
    BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu,
    toNat_small' (n := p.len) (by omega), toNat_small' (n := p.randLen - used) (by omega)]

/-- A loop state with counted candidates left. -/
def StepCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop := LiveCT p T q s ∧ q.2.1 ≠ 0

theorem candidateStep_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (StepCT p T)) (candidateStep c.call) fun _ _ => True := by
  unfold candidateStep
  refine RelCT.seq (two_piece (Ψ := fun q t => StepCT p T q t ∧ t.cf = some (decide (p.randLen - q.1 < p.len)))
    [.esp, .esi, .edi, .ebx] (fun q s₁ s₂ h₁ h₂ => live_pins p T q s₁ s₂ h₁.1 h₂.1) (by taint_decide)
    fun q s ⟨⟨o, hT, L, hf⟩, hk⟩ => WP.mono (stepHead_ok L) fun t ⟨L', hc⟩ => ⟨⟨⟨o, hT, L', hf⟩, hk⟩, hc⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun q t => ShortCT p q.1 t)
      (two_map id (fun q t h => let ⟨⟨⟨o, _, L, _⟩, _⟩, _⟩ := h.1; ⟨o, L.toSearchBase⟩) (zeroOut_ct (fun (_ : Pt) => p)))
      fun q s ⟨⟨⟨⟨o, hT, L, hf⟩, hk⟩, hc⟩, hb⟩ => ?_) (two_map (fun q => q.1) (fun _ _ h => h) (short_ct p))
    have hi := L.input
    have A := hi.abi
    exact WP.mono (zeroOut_ok L.toSearchBase) fun t ⟨⟨hw, hz⟩, kt, syt⟩ =>
      ⟨o, L.toSearchBase.keep kt (by decide) syt (frame_apart hi A.lowO hw L.saved) (out_changes hw),
        (kt.gpr (by decide)).trans L.esi, L.used_le⟩
  · refine RelCT.seq (two_post (Ψ := ClsCT p T) (two_map id (fun q t ⟨⟨⟨⟨o, hT, L, hf⟩, hk⟩, hc⟩, hb⟩ =>
      ⟨⟨o, hT, L, hf⟩, hk, by
        have e : decide (p.randLen - q.1 < p.len) = false := Option.some.inj (hc.symm.trans hb)
        have := of_decide_eq_false e
        have := L.used_le
        show q.1 + p.len ≤ p.randLen
        omega⟩) (candidateRun_ct c p T))
      fun q s ⟨⟨⟨⟨o, hT, L, hf⟩, hk⟩, hc⟩, hb⟩ => ?_) (classify_ct p T)
    have e : decide (p.randLen - q.1 < p.len) = false := Option.some.inj (hc.symm.trans hb)
    have := of_decide_eq_false e
    have := L.used_le
    have hroom : q.1 + p.len ≤ p.randLen := by omega
    exact WP.mono (candidateRun_ok c L hroom) fun t ⟨L', cp⟩ => ⟨o, hT, L', hf, cp, hk, hroom⟩

theorem iteration_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (iteration c.call) fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveCT p T q t ∧ t.zf = some (decide (q.2.1 = 0)))
    [.esp, .esi, .edi, .ebx] (live_pins p T) (by taint_decide) fun q s ⟨o, hT, L, hf⟩ => ?_)
    (RelCT.seq (Q := fun _ _ => True) (R := fun _ _ => True) ?_ ?_)
  · have rem := L.input.remaining_le
    have hk32 : q.2.1 < 2 ^ 32 := by have := L.remaining_le; omega
    exact WP.mono (cmp0_ok L.edi hk32) fun u ⟨⟨he, hr, hm⟩, ku, sy⟩ =>
      ⟨⟨o, hT, L.keep (Keep.drop1 ku hr) sy hm, hf⟩, he⟩
  · refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact two_map id (fun q t h => let ⟨o, _, L, _⟩ := h.1.1; ⟨o, L.toSearchBase⟩)
        (exhausted_ct (fun (_ : Pt) => p))
    · exact two_map id (fun q t h => ⟨h.1.1, fun hk => by
        have := h.1.2.symm.trans h.2; simp at this; exact this hk⟩) (candidateStep_ct c p T)
  · exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide)).mono (fun _ _ _ => ⟨(), trivial, trivial⟩) fun _ _ h => h

end VG.Proof.RsaKeyGen.X86.Search
