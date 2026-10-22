module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-! # The parameter search's exits (x86)

`terminal k` zeros the attempts and the request and sets the status
(`St.terminal`). From a loop state, `exhausted` ends the search with zeros
at the output (`exhausted_ok`); `request` asks for
`min (2 max (left, 256 L), cap)` octets without branching on them
(`requestWords_ok`) and zeros the output (`request_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch Aligned.cons)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- A run's state, with the words a finished search leaves. -/
theorem St.done {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : ParameterSearchResult}
    (hs : ∀ d ∈ doneDs, d ∈ ds) (he : ∀ d ∈ doneDs, f d = doneF (ofState o) (o.gpr .esi) r d)
    (hout : Output (ofState o) r s.mem)
    (hsm : r.remaining ≤ (ofState o).attempts ∧ r.requested ≤ (ofState o).cap ∧ r.used ≤ (ofState o).randLen) :
    Done (ofState o) o r s :=
  ⟨⟨h.abi, rfl⟩, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, (h.words.sub hs).congr he, hout, hsm⟩

/-- `terminal k`: the attempts and the request zero, the status `k`. -/
theorem St.terminal {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (k : Nat) :
    WP isa (.block (VG.Impl.Ffdh.X86.ParamSearch.terminal k)) s fun t =>
      St o (statusOff :: requestOff :: (attemptsOff + 4) :: attemptsOff :: ds)
        (upd (upd (upd (upd f attemptsOff 0) (attemptsOff + 4) 0) requestOff 0) statusOff (BitVec.ofNat 32 k)) t ∧
      Frame [sR o] s.mem t.mem := by
  unfold VG.Impl.Ffdh.X86.ParamSearch.terminal
  refine wp_movi fun t₁ U₁ => ?_
  have S₁ := h.reg U₁ (Or.inl rfl)
  refine S₁.stw hA (d := attemptsOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ F₂ => ?_
  have hA₂ := hA.cons (d := attemptsOff) (by decide) (by decide)
  refine S₂.stw hA₂ (d := attemptsOff + 4) (by decide) (by decide) fun t₃ S₃ G₃ _ _ F₃ => ?_
  have hA₃ := hA₂.cons (d := attemptsOff + 4) (by decide) (by decide)
  refine S₃.stw hA₃ (d := requestOff) (by decide) (by decide) fun t₄ S₄ G₄ _ _ F₄ => ?_
  have hA₄ := hA₃.cons (d := requestOff) (by decide) (by decide)
  refine wp_movi fun t₅ U₅ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw hA₄ (d := statusOff) (by decide) (by decide) fun t₆ S₆ G₆ _ _ F₆ => WP.block_nil ?_
  have e₂ : t₂.gpr .eax = 0 := by rw [G₂, U₁.gpr]
  have e₃ : t₃.gpr .eax = 0 := by rw [G₃, e₂]
  rw [U₁.gpr, e₂, e₃, U₅.gpr] at S₆
  rw [U₅.mem] at F₆
  rw [U₁.mem] at F₂
  exact ⟨S₆, ((F₂.trans F₃).trans F₄).trans F₆⟩

/-- The output, through writes of the state. -/
theorem out_keep {o : State} (A : PSearchABI o) {m m' : Mem} (h : Frame [sR o] m m') :
    Spec.Rsa.bytesAt m' (argumentPointer o 0) (arg o 1).toNat = Spec.Rsa.bytesAt m (argumentPointer o 0) (arg o 1).toNat := by
  have := A.oBound
  refine KeySearch.bytes_frame h (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact A.os

theorem cap_lt {o : State} (A : PSearchABI o) : (ofState o).cap < 2 ^ 27 := by
  have := A.bitsHigh
  simp only [PPub.cap, parameterEntropy, ofState]
  omega

theorem attempts_le {o : State} (A : PSearchABI o) : (ofState o).attempts ≤ 2 ^ 32 := by
  have h := A.attempts
  have hb := A.bitsHigh
  simp only [ofState]
  refine Nat.le_trans h ?_
  unfold parameterAttempts
  have : (arg o 3).toNat * (arg o 3).toNat ≤ 8192 * 8192 := Nat.mul_le_mul hb hb
  omega

theorem exhausted_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa exhausted s (Done p o (.exhausted used)) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  unfold exhausted
  refine WP.seq (WP.mono (S.terminal hA 3) fun t ⟨Sx, _⟩ => ?_)
  have hA₆ : Aligned (statusOff :: requestOff :: (attemptsOff + 4) :: attemptsOff :: liveDs) := by decide
  refine WP.mono (Sx.zeroOut hA₆ (by simp [upd, liveF, ofState, outOff, statusOff, requestOff, attemptsOff])
    (by simp [upd, liveF, ofState, widthOff, statusOff, requestOff, attemptsOff]) (by decide) (by decide))
    fun u ⟨Su, Zo, _, _⟩ => ?_
  refine Su.done (by decide) ?_ Zo ⟨Nat.zero_le _, Nat.zero_le _, h.used_le⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, attemptsOff, ParameterSearchResult.remaining,
      ParameterSearchResult.requested, ParameterSearchResult.status, ParameterSearchResult.used, ofState]

/-! ## The request -/

/-- `x ^ ((y ^ x) & mask)`, the mask all ones or zero: a selection without a branch. -/
theorem select (x y : BitVec 32) (c : Bool) :
    x ^^^ ((y ^^^ x) &&& (if c then BitVec.allOnes 32 else 0)) = if c then y else x := by
  cases c
  · show x ^^^ ((y ^^^ x) &&& 0#32) = x
    rw [BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The selection of the larger of two numbers below `2³²`. -/
theorem select_max {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (if decide ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) then BitVec.ofNat 32 b
      else BitVec.ofNat 32 a) = BitVec.ofNat 32 (max a b) := by
  rw [toNat_ofNat_lt ha, toNat_ofNat_lt hb]
  by_cases h : a < b
  · simp only [h, decide_true, ite_true]; congr 1; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega

/-- The selection of the smaller of two numbers below `2³²`. -/
theorem select_min {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (if decide ((BitVec.ofNat 32 b).toNat < (BitVec.ofNat 32 a).toNat) then BitVec.ofNat 32 b
      else BitVec.ofNat 32 a) = BitVec.ofNat 32 (min a b) := by
  rw [toNat_ofNat_lt ha, toNat_ofNat_lt hb]
  by_cases h : b < a
  · simp only [h, decide_true, ite_true]; congr 1; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega

/-- `k` doublings of `ecx`. -/
theorem doublings_ok {s : State} {v : Nat} (hv : s.gpr .ecx = BitVec.ofNat 32 v) (k : Nat) {rest : List Instr}
    {Q : State → Prop}
    (h : ∀ t, Keeps [.ecx] s t → t.mem = s.mem → t.syms = s.syms → t.gpr .ecx = BitVec.ofNat 32 (2 ^ k * v) →
      WP isa (.block rest) t Q) :
    WP isa (.block (List.replicate k (.alu .add .ecx (.reg .ecx)) ++ rest)) s Q := by
  induction k generalizing s v rest Q with
  | zero => exact h s (Keeps.refl _ _) rfl rfl (by rw [hv, Nat.pow_zero, Nat.one_mul])
  | succ k ih =>
    rw [List.replicate_succ', List.append_assoc]
    refine ih hv (rest := _ :: rest) fun t K m sy e => ?_
    refine wp_add fun t' U _ => ?_
    refine h t' (K.trans (KeySearch.Upd.keeps U)) (U.mem.trans m) (U.syms.trans sy) ?_
    rw [U.gpr, e, BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.two_mul]

theorem St.keeps {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {rs : List Reg}
    (K : Keeps rs s t) (hrs : ∀ r ∈ rs, Scratch r) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : St o ds f t := by
  have nr : ∀ q, (q = .esi ∨ q = .esp ∨ q ∈ calleeSaved) → q ∉ rs := fun q hq hm' => by
    rcases hrs q hm' with rfl | rfl | rfl <;> simp [calleeSaved] at hq
  refine ⟨h.abi, K.2.1.trans h.rd, K.2.2.trans h.wr, hsy.trans h.syms, ?_, ?_, fun q hq hne => ?_,
    hm ▸ h.frame, hm ▸ h.words⟩
  · rw [K.1 _ (nr _ (Or.inr (Or.inl rfl))), h.esp]
  · rw [K.1 _ (nr _ (Or.inl rfl)), h.esi]
  · rw [K.1 _ (nr _ (Or.inr (Or.inr hq))), h.saved q hq hne]

/-- `requestWords`: the request `min (2 max (a, 256 L), c)`, the status 0. -/
theorem St.requestWords {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hl : leftOff ∈ ds) (hw : widthOff ∈ ds) (hc : capOff ∈ ds) {a L c : Nat} (ha : f leftOff = BitVec.ofNat 32 a)
    (hL : f widthOff = BitVec.ofNat 32 L) (hcap : f capOff = BitVec.ofNat 32 c) (ha' : a < 2 ^ 30)
    (hL' : L < 2 ^ 22) (hc' : c < 2 ^ 32) :
    WP isa (.block VG.Impl.Ffdh.X86.ParamSearch.requestWords) s fun t =>
      St o (statusOff :: requestOff :: ds) (upd (upd f requestOff (BitVec.ofNat 32 (min (2 * max a (256 * L)) c)))
        statusOff 0) t := by
  unfold VG.Impl.Ffdh.X86.ParamSearch.requestWords
  simp only [List.cons_append, List.nil_append]
  refine h.ld (Or.inl rfl) hl (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) hw (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine doublings_ok (g₂.trans hL) 8 fun t₃ K₃ m₃ y₃ e₃ => ?_
  have S₃ := S₂.keeps K₃ (fun r hr => by simp at hr; subst hr; exact Or.inr (Or.inl rfl)) m₃ y₃
  have a₃ : t₃.gpr .eax = BitVec.ofNat 32 a := by rw [K₃.1 _ (by decide), o₂ _ (by decide), g₁, ha]
  refine wp_cmp fun t₄ F₄ c₄ _ => ?_
  refine wp_sbb_self c₄ fun t₅ U₅ => ?_
  refine wp_xor fun t₆ U₆ => wp_and fun t₇ U₇ => wp_xor fun t₈ U₈ => wp_add fun t₉ U₉ _ => ?_
  have S₉ := ((((S₃.fupd F₄).reg U₅ (Or.inr (Or.inr rfl))).reg U₆ (Or.inr (Or.inl rfl))).reg U₇
    (Or.inr (Or.inl rfl))).reg U₈ (Or.inl rfl) |>.reg U₉ (Or.inl rfl)
  have x₅ : t₅.gpr .eax = t₃.gpr .eax := by rw [U₅.other _ (by decide), F₄.gpr]
  have y₅ : t₅.gpr .ecx = t₃.gpr .ecx := by rw [U₅.other _ (by decide), F₄.gpr]
  have d₆ : t₆.gpr .edx = _ := (U₆.other _ (by decide)).trans U₅.gpr
  have y₇ : t₇.gpr .ecx = _ := U₇.gpr.trans (by rw [U₆.gpr, d₆])
  have x₇ : t₇.gpr .eax = t₃.gpr .eax := by rw [U₇.other _ (by decide), U₆.other _ (by decide), x₅]
  have v₈ : t₈.gpr .eax = BitVec.ofNat 32 (max a (256 * L)) := by
    rw [U₈.gpr, x₇, y₇, y₅, x₅, a₃, e₃, select, ← select_max (by omega) (by omega)]
  have v₉ : t₉.gpr .eax = BitVec.ofNat 32 (2 * max a (256 * L)) := by
    rw [U₉.gpr, v₈, BitVec.ofNat_add_ofNat, Nat.two_mul]
  refine S₉.ld (Or.inr (Or.inl rfl)) hc (by decide) fun t₁₀ S₁₀ g₁₀ o₁₀ _ _ => ?_
  refine wp_cmp fun t₁₁ F₁₁ c₁₁ _ => ?_
  refine wp_sbb_self c₁₁ fun t₁₂ U₁₂ => ?_
  refine wp_xor fun t₁₃ U₁₃ => wp_and fun t₁₄ U₁₄ => wp_xor fun t₁₅ U₁₅ => ?_
  have S₁₅ := (((S₁₀.fupd F₁₁).reg U₁₂ (Or.inr (Or.inr rfl))).reg U₁₃ (Or.inr (Or.inl rfl))).reg U₁₄
    (Or.inr (Or.inl rfl)) |>.reg U₁₅ (Or.inl rfl)
  have v₁₅ : t₁₅.gpr .eax = BitVec.ofNat 32 (min (2 * max a (256 * L)) c) := by
    have a₁₀ : t₁₀.gpr .eax = BitVec.ofNat 32 (2 * max a (256 * L)) := by rw [o₁₀ _ (by decide), v₉]
    have x₁₂ : t₁₂.gpr .eax = t₁₀.gpr .eax := by rw [U₁₂.other _ (by decide), F₁₁.gpr]
    have y₁₂ : t₁₂.gpr .ecx = t₁₀.gpr .ecx := by rw [U₁₂.other _ (by decide), F₁₁.gpr]
    have d₁₃ : t₁₃.gpr .edx = _ := (U₁₃.other _ (by decide)).trans U₁₂.gpr
    have y₁₄ : t₁₄.gpr .ecx = _ := U₁₄.gpr.trans (by rw [U₁₃.gpr, d₁₃])
    have x₁₄ : t₁₄.gpr .eax = t₁₀.gpr .eax := by rw [U₁₄.other _ (by decide), U₁₃.other _ (by decide), x₁₂]
    rw [U₁₅.gpr, x₁₄, y₁₄, y₁₂, x₁₂, a₁₀, g₁₀, hcap, select, ← select_min (by omega) hc']
  refine S₁₅.stw hA (d := requestOff) (by decide) (by decide) fun t₁₆ S₁₆ _ _ _ _ => ?_
  refine wp_movi fun t₁₇ U₁₇ => ?_
  have S₁₇ := S₁₆.reg U₁₇ (Or.inl rfl)
  refine S₁₇.stw (hA.cons (by decide) (by decide)) (d := statusOff) (by decide) (by decide)
    fun t₁₈ S₁₈ _ _ _ _ => WP.block_nil ?_
  rw [v₁₅, U₁₇.gpr] at S₁₈
  exact S₁₈

theorem request_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa request s (Done p o (.entropy n (parameterRequest p.bits (p.randLen - used)) used)) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  have hc := cap_lt A
  have hr := A.randLen
  have hL := len_pos A
  have hb := A.outLen
  have ec : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl
  have er : (ofState o).randLen = (arg o 6).toNat := rfl
  have el : (ofState o).len = (arg o 1).toNat := rfl
  have eb : (ofState o).bits = (arg o 3).toNat := rfl
  unfold request
  refine WP.seq (WP.mono (S.requestWords hA (by decide) (by decide) (by decide) (a := (ofState o).randLen - used)
    (L := (ofState o).len) (c := (ofState o).cap) (by simp [liveF, leftOff]) (by simp [liveF, widthOff])
    (by simp [liveF, capOff]) (by rw [ec] at hc; omega) (by omega) (by omega))
    fun t St => ?_)
  have hA₄ : Aligned (statusOff :: requestOff :: liveDs) := by decide
  refine WP.mono (St.zeroOut hA₄ (by simp [upd, liveF, ofState, outOff, statusOff, requestOff])
    (by simp [upd, liveF, ofState, widthOff, statusOff, requestOff]) (by decide) (by decide))
    fun u ⟨Su, Zo, _, _⟩ => ?_
  have eq : min (2 * max ((ofState o).randLen - used) (256 * (ofState o).len)) (ofState o).cap =
      parameterRequest (ofState o).bits ((ofState o).randLen - used) := by
    simp only [parameterRequest, PPub.cap, ofState, hb]
  refine Su.done (by decide) ?_ Zo ⟨h.n_le, by rw [ParameterSearchResult.requested, parameterRequest, ec, eb]; omega,
    h.used_le⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, ParameterSearchResult.remaining, eq,
      ParameterSearchResult.requested, ParameterSearchResult.status, ParameterSearchResult.used]

end VG.Proof.Ffdh.X86.PSearch
