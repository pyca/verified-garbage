module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Classify

/-! # The parameter search's loop (x86)

An iteration from a loop state ends the search as the search from there
does, or counts a rejection and loops (`branch_ok`, `iteration_ok`); the
loop, from a loop state, ends in the search from there (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch saved_ne)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem Live.reg {p : PPub} {o s t : State} {used n : Nat} (h : Live p o used n s) {r : Reg}
    {v : BitVec 32} (U : Upd s t r v) (hr : Scratch r) : Live p o used n t := by
  have S := h.st.reg U hr
  obtain ⟨A, rfl⟩ := h.input
  exact S.live h.used_le h.n_le

theorem Live.fupd {p : PPub} {o s t : State} {used n : Nat} (h : Live p o used n s) (F : Fupd s t) :
    Live p o used n t := by
  have S := h.st.fupd F
  obtain ⟨A, rfl⟩ := h.input
  exact S.live h.used_le h.n_le

/-- The attempts' halves are both zero exactly when no attempt is left. -/
theorem halves_zero {n : Nat} (hn : n ≤ 2 ^ 32) :
    ((BitVec.ofNat 32 n ||| BitVec.ofNat 32 (n / 2 ^ 32)) &&& (BitVec.ofNat 32 n ||| BitVec.ofNat 32 (n / 2 ^ 32))
      == 0) = decide (n = 0) := by
  rw [BitVec.and_self]
  by_cases h : n = 2 ^ 32
  · subst h; decide
  · have hlt : n < 2 ^ 32 := by omega
    rw [Nat.div_eq_of_lt hlt, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.or_zero, ofNat_beq_zero hlt]

/-- `mov eax, [esi]; or eax, [esi + 4]; test eax, eax` on the attempts. -/
theorem attempts_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa (.block [.mov .eax (.mem (st attemptsOff)), .alu .or .eax (.mem (st (attemptsOff + 4))),
      .alu .test .eax (.reg .eax)]) s fun t => Live p o used n t ∧ isa.eval .e t = some (decide (n = 0)) := by
  have S := h.st
  have hnl := h.n_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hat := attempts_le A
  refine S.ld (Or.inl rfl) (d := attemptsOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_orS (readSrc_mem (show t₁.gpr .esi = arg o 9 from S₁.esi) (S₁.rIn (d := 4) (by decide)))
    fun t₂ U₂ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine wp_test fun t₃ F₃ z₃ => WP.block_nil ⟨(S₂.fupd F₃).live hul hnl, ?_⟩
  show t₃.zf = _
  rw [z₃, U₂.gpr, g₁, S₁.words.get (d := attemptsOff + 4) (by decide)]
  simp only [liveF, attemptsOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [halves_zero (by omega)]

/-- `room`: the borrow when the tape holds less than a candidate. -/
theorem room_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa (.block room) s fun t => Live p o used n t ∧
      isa.eval .b t = some (decide (p.randLen - used < p.len)) := by
  have S := h.st
  have hnl := h.n_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 6).isLt
  have hL : (ofState o).len < 2 ^ 32 := (arg o 1).isLt
  unfold room
  refine S.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₅ S₅ g₅ _ _ _ => ?_
  refine S₅.ld (Or.inr (Or.inl rfl)) (d := widthOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ _ => ?_
  refine wp_cmp fun t₇ F₇ c₇ _ => WP.block_nil ⟨(S₆.fupd F₇).live hul hnl, ?_⟩
  show t₇.cf = _
  rw [c₇, o₆ .eax (by decide), g₅, g₆]
  simp only [liveF, leftOff, widthOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt hL]

theorem branch_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa branch s (Next p o used n) := by
  have hp := h.input.2
  have A := h.input.1
  have hlen : p.rand.length = p.randLen := by rw [← hp]; exact rand_length
  have hlp := len_pos A
  have hul := h.used_le
  have hlb : p.len = (p.bits + 7) / 8 := by rw [← hp]; exact A.outLen
  have hl64 : 64 ≤ p.len := by rw [← hp]; exact hlp.1
  unfold branch
  refine WP.seq (WP.mono (attempts_ok h) fun t₁ ⟨L₁, e₁⟩ => ?_)
  by_cases hn : n = 0
  · subst hn
    refine WP.ite true (by rw [e₁]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (exhausted_ok L₁) fun v hv => Or.inl ⟨?_, fun h => h.1 rfl⟩
    show Done _ _ (ptail _ _ _ _ _) v
    rw [ptail_zero]; exact hv
  refine WP.ite false (by rw [e₁]; simp [hn]) (fun h => absurd h (by decide)) (fun _ => ?_)
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_ok L₁) fun t₂ ⟨L₂, e₂⟩ => ?_)
  by_cases hr : p.randLen - used < p.len
  · refine WP.ite true (by rw [e₂]; simp [hr]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hs := cand_short (bits := p.bits) (gen := p.gen) (rand := p.rand) (used := used)
      (by rw [hlen, ← hlb]; exact hr)
    have tail := ptail_short hn hs
    refine WP.mono (request_ok L₂) fun v hv => Or.inl ⟨?_, fun ⟨_, h2, _⟩ => by omega⟩
    show Done _ _ (ptail _ _ _ _ _) v
    rw [tail, hlen]
    split
    · rename_i hc
      exfalso
      have hcap : p.len ≤ parameterEntropy p.bits := by rw [hlb]; unfold parameterEntropy; omega
      omega
    · exact hv
  refine WP.ite false (by rw [e₂]; simp [hr]) (fun h => absurd h (by decide)) (fun _ => ?_)
  have hu : used < p.randLen := by omega
  refine WP.seq (WP.mono (attempt_ok L₂ hu) fun u ⟨Su, eu, ou, cu⟩ => ?_)
  obtain ⟨_, rfl⟩ := L₂.input
  exact classify_ok L₂ Su eu ou cu hn (by omega)

theorem Done.reg {p : PPub} {o s t : State} {r : ParameterSearchResult} (h : Done p o r s) {q : Reg}
    {v : BitVec 32} (U : Upd s t q v) (hq : Scratch q) : Done p o r t := by
  obtain ⟨A, rfl⟩ := h.input
  refine ⟨⟨A, rfl⟩, U.rd.trans h.rd, U.wr.trans h.wr, U.syms.trans h.syms, ?_, ?_, fun r' hr hne => ?_,
    U.mem ▸ h.frame, U.mem ▸ h.words, U.mem ▸ h.output, h.small⟩
  · rw [U.other _ (saved_ne hq (by decide)), h.esp]
  · rw [U.other _ (saved_ne hq (by decide)), h.esi]
  · rw [U.other _ (saved_ne hq hr), h.saved r' hr hne]

theorem Done.fupd {p : PPub} {o s t : State} {r : ParameterSearchResult} (h : Done p o r s) (F : Fupd s t) :
    Done p o r t :=
  ⟨h.input, F.rd.trans h.rd, F.wr.trans h.wr, F.syms.trans h.syms, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words, F.mem ▸ h.output,
    h.small⟩

theorem status_le (r : ParameterSearchResult) : r.status ≤ 3 := by
  unfold ParameterSearchResult.status; split <;> decide

/-- What an iteration leaves: the search finished as `R`, or a loop state with fewer attempts from
which it ends as `R`, and the loop's condition says which. -/
def IterPost (p : PPub) (o : State) (R : ParameterSearchResult) (n : Nat) (s : State) : Prop :=
  (isa.eval .e s = some false ∧ Done p o R s) ∨
    (isa.eval .e s = some true ∧ ∃ m < n, ∃ used, Live p o used m s ∧ p.tail used m = R)

/-- The loop's condition, `mov eax, [esi + 68]; cmp eax, 4`. -/
abbrev guard : List Instr := [.mov .eax (.mem (st statusOff)), .alu .cmp .eax (.imm 4)]

theorem guard_done {p : PPub} {o v : State} {r : ParameterSearchResult} (D : Done p o r v) :
    WP isa (.block guard) v fun t => isa.eval .e t = some false ∧ Done p o r t := by
  have A := D.input.1
  have hp := D.input.2
  have dS : v.gpr .esi = arg o 9 := by rw [D.esi, ← hp]; rfl
  refine wp_ldm dS (by rw [D.rd, D.wr]; exact ⟨_, List.mem_append_right _ (sR_mem A), st_in A (by decide)⟩)
    fun t₁ U₁ => wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ⟨?_, (D.reg U₁ (Or.inl rfl)).fupd F₂⟩
  subst hp
  have w : v.mem.readW (addr (arg o 9) statusOff) 32 = doneF (ofState o) (o.gpr .esi) r statusOff :=
    D.words.get (by decide)
  have := status_le r
  show t₂.zf = _
  rw [z₂, U₁.gpr, w]
  simp only [doneF, statusOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_beq (by omega) (by decide)]
  simp only [Option.some.injEq, decide_eq_false_iff_not]
  omega

theorem guard_rej {p : PPub} {o v : State} {used n : Nat} (R : Rej p o used n v) :
    WP isa (.block guard) v fun t => isa.eval .e t = some true ∧ Live p o used n t := by
  obtain ⟨L, hst⟩ := R
  have A := L.input.1
  have hp := L.input.2
  have lS : v.gpr .esi = arg o 9 := by rw [L.esi, ← hp]; rfl
  refine wp_ldm lS (by rw [L.rd, L.wr]; exact ⟨_, List.mem_append_right _ (sR_mem A), st_in A (by decide)⟩)
    fun t₁ U₁ => wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ⟨?_, (L.reg U₁ (Or.inl rfl)).fupd F₂⟩
  show t₂.zf = _
  rw [z₂, U₁.gpr, show v.mem.readW (addr (arg o 9) statusOff) 32 = 4 by rw [← hp] at hst; exact hst]
  rfl

theorem iteration_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa iteration s (IterPost p o (p.tail used n) n) := by
  unfold iteration
  refine WP.seq (WP.mono (branch_ok h) fun v hv => ?_)
  rcases hv with ⟨D, _⟩ | ⟨⟨hn, _, rest, hc⟩, Rj⟩
  · exact WP.mono (guard_done D) fun t ⟨he, Dt⟩ => Or.inl ⟨he, Dt⟩
  · exact WP.mono (guard_rej Rj) fun t ⟨he, Lt⟩ =>
      Or.inr ⟨he, n - 1, by omega, _, Lt, (ptail_reject hn hc).symm⟩

theorem loop_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa (.loop iteration .e) s (Done p o (p.tail used n)) := by
  refine WP.loop (M := isa) (fun m t => ∃ u, Live p o u m t ∧ p.tail u m = p.tail used n)
    (fun m t ⟨u, L, hS⟩ => ?_) _ s ⟨used, h, rfl⟩
  refine WP.mono (iteration_ok L) fun v hv => ?_
  rcases hv with ⟨he, D⟩ | ⟨he, m', hm, u', L', hS'⟩
  · exact Or.inl ⟨he, hS ▸ D⟩
  · exact Or.inr ⟨he, m', hm, u', L', hS'.trans hS⟩

end VG.Proof.Ffdh.X86.PSearch
