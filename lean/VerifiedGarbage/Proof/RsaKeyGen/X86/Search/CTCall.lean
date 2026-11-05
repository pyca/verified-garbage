module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTLeaf
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Call
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTLeaf
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Call
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
meta import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # Two runs of the candidate (i686)

Two runs at the same loop point, whose public data agree, pass
`vg_rsa_keygen_candidate` the same arguments, at the same stack pointer,
and the same public data: `e` and the candidate's leak, which the trace
fixes (`callee_pub`); so their calls leak the same (`call_ct`), and so do
their frames of arguments (`candidateRun_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Search

/-- Two entry states with the same public data have the same arguments. -/
theorem args_eq {p : SearchPublic} {o₁ o₂ : State} (h₁ : SearchInput p o₁) (h₂ : SearchInput p o₂) {i : Nat}
    (hi : i < 11) : arg o₁ i = arg o₂ i := by
  have e : searchOfState o₁ = searchOfState o₂ := h₁.2.trans h₂.2.symm
  have ofn : ∀ {x y : BitVec 32}, x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg SearchPublic.op e
  · exact ofn (congrArg SearchPublic.len e)
  · exact congrArg SearchPublic.up e
  · exact congrArg SearchPublic.ep e
  · exact ofn (congrArg SearchPublic.elen e)
  · exact congrArg SearchPublic.pp e
  · exact ofn (congrArg SearchPublic.plen e)
  · exact congrArg SearchPublic.rp e
  · exact ofn (congrArg SearchPublic.randLen e)
  · exact congrArg SearchPublic.B e
  · exact ofn (congrArg SearchPublic.words e)

theorem callArg_eq {p : SearchPublic} {o₁ o₂ : State} (h₁ : SearchInput p o₁) (h₂ : SearchInput p o₂)
    (used : Nat) {j : Nat} (hj : j < 11) : callArg o₁ used j = callArg o₂ used j := by
  simp only [callArg, args_eq h₁ h₂ (i := 7) (by omega), args_eq h₁ h₂ (i := 8) (by omega), args_eq h₁ h₂ hj]

/-- In the candidate's frame, with its arguments, at the loop point `q`. -/
def CallCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  ∃ o s₀, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s₀ ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ Fr p o s₀ t ∧ ArgsAt o q.1 11 t.mem ∧
    q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen

theorem used_lt {p : SearchPublic} {o : State} (h : SearchInput p o) {used : Nat} (hr : used + p.len ≤ p.randLen) :
    used < (arg o 8).toNat := by
  have : p.randLen = (arg o 8).toNat := by rw [← h.2]; rfl
  have := h.len_valid
  omega

theorem callee_pub {p : SearchPublic} {T : List Nat} {q : Pt} {t₁ t₂ : State} (h₁ : CallCT p T q t₁)
    (h₂ : CallCT p T q t₂) (rd wr : List Region) :
    VG.Proof.RsaKeyGen.X86.Candidate.contract.pub (t₁.callEntry.withRegions rd wr)
      (t₂.callEntry.withRegions rd wr) := by
  obtain ⟨o₁, s₁, T₁, L₁, f₁, F₁, a₁, hk, hr⟩ := h₁
  obtain ⟨o₂, s₂, T₂, L₂, f₂, F₂, a₂, -, -⟩ := h₂
  have i₁ := F₁.input
  have i₂ := F₂.input
  obtain ⟨b₁E, b₁P, b₁W⟩ := entry_bytes F₁ (used_lt i₁ hr) (t₁.unknowns 0)
  obtain ⟨b₂E, b₂P, b₂W⟩ := entry_bytes F₂ (used_lt i₂ hr) (t₂.unknowns 0)
  have e₁ : searchE o₁ = p.eB := by rw [← i₁.2]; rfl
  have e₂ : searchE o₂ = p.eB := by rw [← i₂.2]; rfl
  have l₁ : (arg o₁ 1).toNat = p.len := by rw [← i₁.2]; rfl
  have l₂ : (arg o₂ 1).toNat = p.len := by rw [← i₂.2]; rfl
  sig_pub [VG.Proof.RsaKeyGen.X86.Candidate.contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  simp only [ce_arg i₁ F₁.esp a₁ rd wr (show 0 < 11 by decide), ce_arg i₁ F₁.esp a₁ rd wr (show 1 < 11 by decide),
    ce_arg i₁ F₁.esp a₁ rd wr (show 2 < 11 by decide), ce_arg i₁ F₁.esp a₁ rd wr (show 3 < 11 by decide),
    ce_arg i₁ F₁.esp a₁ rd wr (show 4 < 11 by decide), ce_arg i₁ F₁.esp a₁ rd wr (show 5 < 11 by decide),
    ce_arg i₁ F₁.esp a₁ rd wr (show 6 < 11 by decide), ce_arg i₁ F₁.esp a₁ rd wr (show 7 < 11 by decide),
    ce_arg i₁ F₁.esp a₁ rd wr (show 8 < 11 by decide), ce_arg i₁ F₁.esp a₁ rd wr (show 9 < 11 by decide),
    ce_arg i₁ F₁.esp a₁ rd wr (show 10 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 0 < 11 by decide), ce_arg i₂ F₂.esp a₂ rd wr (show 1 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 2 < 11 by decide), ce_arg i₂ F₂.esp a₂ rd wr (show 3 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 4 < 11 by decide), ce_arg i₂ F₂.esp a₂ rd wr (show 5 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 6 < 11 by decide), ce_arg i₂ F₂.esp a₂ rd wr (show 7 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 8 < 11 by decide), ce_arg i₂ F₂.esp a₂ rd wr (show 9 < 11 by decide),
    ce_arg i₂ F₂.esp a₂ rd wr (show 10 < 11 by decide)]
  have ca := fun j (hj : j < 11) => callArg_eq i₁ i₂ q.1 hj
  refine ⟨?_, ?_, ?_, ca 0 (by decide), ca 1 (by decide), ca 2 (by decide), ca 3 (by decide), ca 4 (by decide),
    ca 5 (by decide), ca 6 (by decide), ca 7 (by decide), ca 8 (by decide), ca 9 (by decide), ca 10 (by decide)⟩
  · simp only [F₁.esp, F₂.esp]
  · rw [F₁.syms, F₂.syms]
    exact congrArg SearchPublic.tab (i₁.2.trans i₂.2.symm)
  · simp only [callArg, Nat.reduceEqDiff, ↓reduceIte,
      ret_addr i₁ F₁.esp, ret_addr i₂ F₂.esp, b₁E, b₁P, b₁W, b₂E, b₂P, b₂W]
    rw [e₁, e₂, l₁, l₂, ← leak_of T₁ f₁ hk, ← leak_of T₂ f₂ hk]

/-- What the callee reads and writes, from the public data. -/
abbrev callRdK (p : SearchPublic) (used : Nat) : List Region :=
  [⟨p.ep.setWidth 64, p.elen⟩, ⟨p.pp.setWidth 64, p.plen⟩,
    ⟨(p.rp + BitVec.ofNat 32 used).setWidth 64, p.randLen - used⟩, ⟨p.tab.setWidth 64, 8192⟩]
abbrev callWrK (p : SearchPublic) : List Region :=
  [⟨p.op.setWidth 64, p.len⟩, ⟨p.up.setWidth 64, 8⟩, ⟨p.B.setWidth 64, p.words * 8⟩,
    ⟨p.sp.setWidth 64 - 216#64 + BitVec.ofNat 64 156, 44⟩]

theorem callRd_eq {p : SearchPublic} {o : State} (h : SearchInput p o) (used : Nat) :
    callRd o used = callRdK p used := by
  rw [← h.2, callRd, tableRs_eq]; rfl

theorem callWr_eq {p : SearchPublic} {o : State} (h : SearchInput p o) : callWr o = callWrK p := by
  rw [← h.2]; rfl

theorem call_ct (c : Cand) (p : SearchPublic) (T : List Nat) (q : Pt) :
    RelCT isa (fun t₁ t₂ => CallCT p T q t₁ ∧ CallCT p T q t₂) c.call fun _ _ => True := by
  refine RelCT.call c.verified.1 c.verified.2.1 (callRdK p q.1) (callWrK p) fun t₁ t₂ ⟨h₁, h₂⟩ => ?_
  have pub := callee_pub h₁ h₂ (callRdK p q.1) (callWrK p)
  obtain ⟨o₁, s₁, -, L₁, -, F₁, a₁, -, hr⟩ := h₁
  obtain ⟨o₂, s₂, -, L₂, -, F₂, a₂, -, -⟩ := h₂
  have i₁ := F₁.input
  have i₂ := F₂.input
  have c₁ := call_covers F₁ (used_lt i₁ hr)
  have c₂ := call_covers F₂ (used_lt i₂ hr)
  rw [callRd_eq i₁, callWr_eq i₁] at c₁
  rw [callRd_eq i₂, callWr_eq i₂] at c₂
  refine ⟨?_, ?_, pub, c₁.1, c₁.2, c₂.1, c₂.2, by rw [F₁.esp, F₂.esp]⟩
  · rw [← callRd_eq i₁, ← callWr_eq i₁]; exact call_pre i₁ hr F₁.esp a₁ F₁.syms F₁.frame
  · rw [← callRd_eq i₂, ← callWr_eq i₂]; exact call_pre i₂ hr F₂.esp a₂ F₂.syms F₂.frame

/-- Relating two runs for each public datum. -/
theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

/-- A loop state from which the candidate runs. -/
def RunCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  LiveCT p T q s ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen

/-- In the candidate's frame, before its arguments. -/
def FrCT (p : SearchPublic) (T : List Nat) (q : Pt) (f : State) : Prop :=
  ∃ s, RunCT p T q s ∧ f = allocFrame 44 s

theorem frCT_pins (p : SearchPublic) (T : List Nat) : Pins (FrCT p T) [.esi, .esp] := by
  intro q f₁ f₂ ⟨s₁, ⟨⟨_, _, L₁, _⟩, _⟩, e₁⟩ ⟨s₂, ⟨⟨_, _, L₂, _⟩, _⟩, e₂⟩ r hr
  subst e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), L₁.esi, L₂.esi]
  · rw [allocFrame_esp, allocFrame_esp, L₁.sp, L₂.sp]

theorem candidateRun_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (RunCT p T)) (candidateRun c.call) fun _ _ => True := by
  unfold candidateRun
  rw [show 4 * callWords = 44 from rfl]
  refine RelCT.frameAlloc ((RelCT.seq (two_piece (Ψ := CallCT p T) [.esi, .esp] (frCT_pins p T) (by taint_decide)
    fun q f ⟨s, h, e⟩ => ?_) (two_of (call_ct c p T))).mono
      (fun a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩ => ⟨q, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩) fun _ _ h => h)
  subst e
  obtain ⟨⟨o, hT, L, hf⟩, hk, hr⟩ := h
  exact WP.mono (arguments_ok L.toSearchBase.alloc L.esi) fun t ⟨F, a⟩ => ⟨o, s, hT, L, hf, F, a, hk, hr⟩

end VG.Proof.RsaKeyGen.X86.Search
