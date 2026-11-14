module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2
public import VerifiedGarbage.Proof.Rsa.X86.Rd.DivQ
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Step
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # `wordDivQ`'s timing on i686

`RecoverDetRt.wordDivQ` (`Rd/DivQ.lean` has its run): its start is a leaf; each digit step is three
(`oSteps`, the steps left, is read after the step's stores of secrets). The frames at the leaves'
boundaries are `wordDivQ_ok`'s and `digitStepQ_ok`'s first parts (`wdqPre_ok`, `dsA_ok`, `dsB_ok`);
the rest of each run is carried as its correctness and its run on the view.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.WordRt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oQ oU0 oU2 oSteps oDig h0)
open VG.Impl.Rsa.X86.RecoverDetRt (sQd)

/-- `wordDivQ`'s start. -/
abbrev wdqPre (ml x r m : Nat) (extra : Bool) : List (Prog isa) :=
  [.block (VG.Impl.Rsa.X86.WordModRt.orTop VG.Impl.Rsa.X86.RecoverRt.wid ml m),
    VG.Impl.Rsa.X86.WordModRt.recip VG.Impl.Rsa.X86.RecoverRt.wid,
    VG.Impl.Rsa.X86.RecoverDetRt.seedX ml x r extra]

/-- The digit step's first block: the dividend's word brought down into `oDig`. -/
abbrev dq1 (x : Nat) : Prog isa :=
  .block (arrPtr VG.Impl.Rsa.X86.RecoverRt.wid .ebx x .edx ++ [.mov .eax (.mem (sc oSteps)),
    .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .mov .eax (.mem (at_ .ebx 0)), .store (sc oDig) .eax])

/-- The digit step's third block: the digit stored over the word brought down. -/
abbrev dq3 (x : Nat) : Prog isa :=
  .block (arrPtr VG.Impl.Rsa.X86.RecoverRt.wid .ebx x .edx ++ [.mov .eax (.mem (sc oSteps)),
    .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .mov .eax (.mem (sc sQd)), .store (at_ .ebx 0) .eax])

/-- The digit step's count down. -/
abbrev dq4 : Prog isa :=
  .block [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .store (sc oSteps) .eax]

abbrev dqA (ml x r m t : Nat) : List (Prog isa) := [dq1 x, VG.Impl.Rsa.X86.RecoverDetRt.stepQ ml r m t]

theorem digitStepQ_eq (ml x r m t : Nat) :
    VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t = VG.Impl.Rsa.X86.Keys.seqs (dqA ml x r m t ++ [dq3 x, dq4]) :=
  rfl

theorem wordDivQ_eq (ml x r m t : Nat) (extra : Bool) :
    VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ ml x r m t extra = VG.Impl.Rsa.X86.Keys.seqs (wdqPre ml x r m extra ++
      ([.loop (VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t) .ne] : List (Prog isa))) :=
  rfl

section
variable {B : Addr} {Z len N : Nat}

/-- `wordDivQ`'s start: the divisor's top bit set, its reciprocal, the remainder seeded. -/
theorem wdqPre_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {ml a x r m t : Nat}
    {extra : Bool} (hm : MLen s B Z ml a) (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N)
    (_hrt : r ≠ t) (_hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (_hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (wdqPre ml x r m extra)) s fun u₃ =>
      ∃ Mn X₀, val32 u₃.mem B (arr (kw len) x) (xn len extra) = X₀ ∧
        val32 u₃.mem B (arr (kw len) m) (wq a) = Mn ∧ StepHdr u₃.mem B Mn (wq a) ∧
        LoopQ u₃ B Z len N ml a x r t Mn X₀ (xn len extra - wq a + 1) 0 u₃ ∧
        Outside B 0 Z s.mem u₃.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u₃ := by
  have nw := h.ws.workspace.nowrap
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  have xnb : kw len ≤ xn len extra ∧ xn len extra ≤ kw len + 1 := by cases extra <;> simp [xn]
  have fx := h.ws.arr_fit hx
  simp only [S] at fx
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The divisor's top bit, `d`, `d₁` and `v`.
  refine WP.seq (WP.mono (orTop_ok h hm hmN (by omega_using [h4]) hw) fun u₁ ⟨h₁, k₁, w₁, t₁, d₁, d1₁, K₁⟩ => ?_)
  obtain ⟨Mn, hMn⟩ : ∃ Mn, Mn = val32 u₁.mem B (arr (kw len) m) (wq a) := ⟨_, rfl⟩
  have hMsplit : Mn = val32 u₁.mem B (arr (kw len) m) (wq a - 1) +
      2 ^ (32 * (wq a - 1)) * mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMn, show wq a = wq a - 1 + 1 by omega_using [h4], val32_succ, Nat.add_sub_cancel]
  have htop : mw u₁.mem B (kw len) m (wq a - 1) < 2 ^ 32 := (u₁.mem.readW _ 32).isLt
  have hdiv : Mn / 2 ^ (32 * (wq a - 1)) = mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMsplit, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _),
      Nat.add_zero]
  have hdn : 2 ^ 31 ≤ Mn / 2 ^ (32 * (wq a - 1)) := by rw [hdiv, t₁]; omega_using []
  refine WP.seq (WP.mono (recip_ok h₁ (d := Mn / 2 ^ (32 * (wq a - 1))) (by rw [hdiv]; exact d₁) hdn
    (by rw [hdiv]; exact htop)) fun u₂ ⟨h₂, k₂, v₂, K₂⟩ => ?_)
  have Hd : StepHdr u₂.mem B Mn (wq a) := by
    refine ⟨?_, hdn, ?_, v₂, by rw [hMn]; exact val32_lt _ _ _ _⟩
    · rw [k₂.slot (by decide) (by decide), d₁, hdiv]
    · rw [k₂.slot (by decide) (by decide), d1₁, ← w₁ (wq a - 2) (by omega_using [hw]) (by omega_using [h4]), hMn]
      exact w32_of_val32 u₁.mem B (by omega_using [h4])
  have K₀₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := (K₁.mono (by decide)).trans K₂
  have k₀₂ : Keep B (kw len) [m] [oD, oD1, oV] s.mem u₂.mem :=
    (k₁.mono (by simp) (by simp)).trans (k₂.mono (by simp) (by simp))
  have Z₀₂ := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₀₂ (by simpa using hmN) (by decide)
  have hm₂ : MLen u₂ B Z ml a := hm.keep K₀₂ (by decide) Z₀₂
  -- `r` seeded with the dividend's top words.
  refine WP.mono (seedX_ok h₂ hm₂ hx hr hxr (extra := extra) (by omega_using [h4]) hw) fun u₃ ⟨h₃, k₃, v₃, st₃, K₃⟩ => ?_
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = val32 s.mem B (arr (kw len) x) (xn len extra) := ⟨_, rfl⟩
  have xs₂ : ∀ j, j < kw len + 2 → w32 u₂.mem B (arr (kw len) x + 4 * j) = w32 s.mem B (arr (kw len) x + 4 * j) :=
    fun j hj => k₀₂.word (j := x) (i := j) (by simp only [S]; omega_using [hj]) (by simpa using hxm) (by decide)
      (h.ws.fit64 hx)
  have xs₃ : ∀ j, j < kw len + 2 → w32 u₃.mem B (arr (kw len) x + 4 * j) = w32 s.mem B (arr (kw len) x + 4 * j) :=
    fun j hj => by
      rw [k₃.word (j := x) (i := j) (by simp only [S]; omega_using [hj]) (by simpa using hxr) (by decide)
        (h.ws.fit64 hx)]
      exact xs₂ j hj
  have X₂ : val32 u₂.mem B (arr (kw len) x) (xn len extra) = X₀ := by
    rw [hX₀]; exact val32_congr fun j hj => xs₂ j (by omega_using [xnb, hj])
  have X₃ : val32 u₃.mem B (arr (kw len) x) (xn len extra) = X₀ := by
    rw [hX₀]; exact val32_congr fun j hj => xs₃ j (by omega_using [xnb, hj])
  have M₃ : val32 u₃.mem B (arr (kw len) m) (wq a) = Mn := by
    rw [hMn]
    exact val32_congr fun j hj => ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := j) (by simp only [S]; omega_using [hw, hj]) (by simpa using hrm)
      (by decide) (h.ws.fit64 hmN)
  have H₃ : StepHdr u₃.mem B Mn (wq a) := Hd.keep (k₃.slot (by decide) (by decide))
    (k₃.slot (by decide) (by decide)) (k₃.slot (by decide) (by decide))
  have hXlt : X₀ < 2 ^ (32 * xn len extra) := by rw [hX₀]; exact val32_lt _ _ _ _
  have hseed : val32 u₃.mem B (arr (kw len) r) (kw len + 1) < 2 ^ (32 * (wq a - 1)) := by
    rw [v₃, X₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 * (wq a - 1) + 32 * (xn len extra - (wq a - 1)) = 32 * xn len extra by omega_using [hw, xnb]]
    exact hXlt
  have hMlow : 2 ^ (32 * (wq a - 1)) ≤ Mn := by
    rw [hMsplit, t₁]
    have := Nat.mul_le_mul_left (2 ^ (32 * (wq a - 1))) (show 1 ≤ mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 by omega_using [])
    omega_using [this]
  have hz : ∀ j, wq a - 1 ≤ j → j < kw len + 1 → w32 u₃.mem B (arr (kw len) r + 4 * j) = 0 :=
    fun j h1 h2 => val32_word_zero (n := kw len + 1) h2 h1 hseed
  have hr0 : val32 u₃.mem B (arr (kw len) r) (wq a) = val32 u₃.mem B (arr (kw len) r) (kw len + 1) := by
    rw [show kw len + 1 = wq a + (kw len + 1 - wq a) by omega_using [hw], val32_append,
      val32_zero_of (n := kw len + 1 - wq a) fun j hj => by
        rw [show arr (kw len) r + 4 * wq a + 4 * j = arr (kw len) r + 4 * (wq a + j) by omega_using []]
        exact hz _ (by omega_using []) (by omega_using [hj]),
      Nat.mul_zero, Nat.add_zero]
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = xn len extra - wq a + 1 := ⟨_, rfl⟩
  have topq : X₀ / 2 ^ (32 * Sc) < Mn := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    refine Nat.lt_of_lt_of_le hXlt ?_
    have := Nat.mul_le_mul_right (2 ^ (32 * Sc)) hMlow
    rw [← Nat.pow_add, show 32 * (wq a - 1) + 32 * Sc = 32 * xn len extra by omega_using [h4, hw, xnb, hSc]] at this
    exact this
  have I₀ : LoopQ u₃ B Z len N ml a x r t Mn X₀ Sc 0 u₃ := by
    refine ⟨h₃, hm₂.keep K₃ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₂.ws k₃ (by simpa using hr)
      (by decide)), Keep.refl _ _ _ _ _, Keeps.refl _ _, ?_, ?_, ?_, fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
    · rw [hr0, Nat.sub_zero, show Sc = xn len extra - (wq a - 1) by omega_using [h4, hw, xnb, hSc], ← X₂, ← v₃,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hseed hMlow)]
    · intro j hj1 hj2; exact hz j (by omega_using [hj1]) hj2
    · rw [st₃, hSc, Nat.sub_zero]
    · rw [Nat.sub_zero, Nat.div_eq_of_lt topq]; rfl

  rw [hSc] at I₀
  refine ⟨Mn, X₀, X₃, M₃, H₃, I₀, VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws
    ((k₀₂.mono (js' := [m, r, t, x]) (ds' := [oD, oD1, oV, oMask, oSteps, oQ, oU0, oU2, oDig, sQd]) (by simp)
      (by simp)).trans (k₃.mono (by simp) (by simp))) (by simp; omega_using [hx, hr, hmN, ht]) (by decide),
    (K₀₂.mono (by decide)).trans (K₃.mono (by decide))⟩

/-- The digit step's first part: the digit brought down, the step; its frame. -/
theorem dsA_ok {s₀ u : State} {ml a x r m t : Nat} {extra : Bool} {M X₀ Sc i : Nat}
    (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t)
    (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len)
    (hX : val32 s₀.mem B (arr (kw len) x) (xn len extra) = X₀) (hM : val32 s₀.mem B (arr (kw len) m) (wq a) = M)
    (H : StepHdr s₀.mem B M (wq a)) (hS : Sc = xn len extra - wq a + 1) (hi : i < Sc)
    (I : LoopQ s₀ B Z len N ml a x r t M X₀ Sc i u) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (dqA ml x r m t)) u fun v =>
      RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N ∧ Outside B 0 Z u.mem v.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u v ∧ slot v.mem B oSteps = Sc - i := by
  have h := I.ws
  have nw := h.ws.workspace.nowrap
  have fx := h.ws.arr_fit hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have xnb : kw len ≤ xn len extra ∧ xn len extra ≤ kw len + 1 := by cases extra <;> simp [xn]
  have nQ : ∀ d ∈ [sQd], d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp only [List.mem_singleton, forall_eq]; decide
  have Mu : val32 u.mem B (arr (kw len) m) (wq a) = M := by
    rw [← hM]
    exact val32_congr fun j hj => I.keep.word (j := m) (i := j) (by simp only [S]; omega)
      (by simp; omega) (by decide) (h.ws.fit64 hmN)
  have Hu : StepHdr u.mem B M (wq a) := H.keep (I.keep.slot (by decide) (by decide))
    (I.keep.slot (by decide) (by decide)) (I.keep.slot (by decide) (by decide))
  have hM0 : 0 < M := by have := H.dn; rcases Nat.eq_zero_or_pos M with e | e <;> simp_all
  -- The digit.
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (xPtr_ok h hx I.steps (by omega) (by omega) fun u₆ K₁₆ m₆ p₆ => ?_)
  refine wp_movS (readSrc_ptr (h.rt.of_keeps K₁₆) p₆ (d := 0) (by omega)) fun u₇ U₇ _ => ?_
  have K₁₇ : Keeps [.eax, .ebx, .edx] u u₇ := K₁₆.trans (U₇.keeps.mono (by decide))
  have h₇ := h.keep K₁₇ (by decide) (by decide) (by rw [U₇.mem, m₆]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h₇ (d := oDig) (by decide) .eax) fun u₈ ⟨h₈, k₈, e₈, K₈⟩ => ?_
  have Z₈ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₇.ws k₈ (by simp) (by decide)
  have K₀₈ : Keeps [.eax, .ebx, .edx] u u₈ := K₁₇.trans (K₈.mono (by simp))
  have Zu₈ : Outside B 0 Z u.mem u₈.mem := by rw [U₇.mem, m₆] at Z₈; exact Z₈
  have hm₈ : MLen u₈ B Z ml a := I.ml.keep K₀₈ (by decide) Zu₈
  have k₀₈ : Keep B (kw len) [] [oDig] u.mem u₈.mem := by rw [U₇.mem, m₆] at k₈; exact k₈
  have R₈ : val32 u₈.mem B (arr (kw len) r) (wq a) = X₀ / 2 ^ (32 * (Sc - i)) % M := by
    rw [← I.val]
    exact val32_congr fun j hj => k₀₈.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hr)
  have M₈ : val32 u₈.mem B (arr (kw len) m) (wq a) = M := by
    rw [← Mu]
    exact val32_congr fun j hj => k₀₈.word (j := m) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hmN)
  have H₈ : StepHdr u₈.mem B M (wq a) := Hu.keep (k₀₈.slot (by decide) (by decide))
    (k₀₈.slot (by decide) (by decide)) (k₀₈.slot (by decide) (by decide))
  -- The step.
  refine WP.mono (stepQ_ok h₈ hm₈ hr hmN ht hrt hmt h4 hw M₈ R₈ (Nat.mod_lt _ hM0) H₈)
    fun v₁ ⟨hv₁, kv₁, _, _, sv₁, _, Kv₁⟩ => ?_
  have st : slot v₁.mem B oSteps = Sc - i := by rw [sv₁, k₀₈.slot (by decide) (by decide)]; exact I.steps
  exact ⟨hv₁, VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws ((k₀₈.mono (js' := [r, t, x])
      (ds' := [oMask, oSteps, oQ, oU0, oU2, oDig, sQd]) (by simp) (by simp)).trans (kv₁.mono (by simp) (by simp)))
    (by simp; omega) (by decide), (K₀₈.mono (by decide)).trans Kv₁, st⟩

/-- The digit stored over the dividend's word `St - 1`: its frame. -/
theorem dsB_ok {v : State} (hv₁ : RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N) {x St : Nat} (hx : x < N)
    (st : slot v.mem B oSteps = St) (h1 : 1 ≤ St) (h2 : St ≤ kw len + 2) :
    WP isa (dq3 x) v fun w => RtWs VG.Impl.Rsa.X86.RecoverRt.wid w B Z len N ∧ Outside B 0 Z v.mem w.mem ∧
      Keeps [.eax, .ebx, .edx] v w ∧ slot w.mem B oSteps = St := by
  have nw := hv₁.ws.workspace.nowrap
  have fx := hv₁.ws.arr_fit hx
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound hv₁.lenLe
  simp only [S] at fx
  refine xPtr_ok hv₁ hx st h1 h2 fun w₆ KW₆ mw₆ pw₆ => ?_
  refine wp_movS (readHdr (hv₁.ws.rest KW₆) (d := sQd) (by decide)) fun w₇ W₇ _ => ?_
  have KW₇ : Keeps [.eax, .ebx, .edx] v w₇ := KW₆.trans (W₇.keeps.mono (by decide))
  have wsw := (hv₁.rt.of_keeps KW₇)
  have pw₇ : PtrAt w₇ B .ebx (arr (kw len) x + 4 * (St - 1)) := by
    rw [PtrAt, W₇.other _ (by decide)]; exact pw₆
  refine wp_storeS (ea_ptr wsw pw₇ (d := 0) (by omega_using [h2, fx])) (ws_write wsw (by omega_using [h2, fx])) fun w₈ MW₈ => WP.block_nil ?_
  have m₈ : w₈.mem = v.mem.writeW (off B (arr (kw len) x + 4 * (St - 1))) (w₇.gpr .eax) := by
    rw [MW₈.mem, W₇.mem, mw₆, Nat.add_zero]
  have Ox := writeW32_outside v.mem B (d := arr (kw len) x + 4 * (St - 1)) (w₇.gpr .eax) (by omega_using [h2, nw, fx])
  rw [← m₈] at Ox
  have kx : Keep B (kw len) [x] [] v.mem w₈.mem :=
    Keep.of_arr (d := 4 * (St - 1)) Ox (by simp only [S]; omega_using [h2]) (by simp)
  have KW₈ : Keeps [.eax, .ebx, .edx] v w₈ := KW₇.trans ((MW₈.keeps []).mono (by simp))
  have O₈ := VG.Proof.Rsa.X86.KeyRt.keep_outside hv₁.ws kx (by simpa using hx) (by simp)
  exact ⟨hv₁.keep KW₈ (by decide) (by decide) O₈, O₈, KW₈, by rw [kx.slot (e := oSteps) (by decide) (by simp)]; exact st⟩

theorem wp_seqs_app {x y : Prog isa} {xs ys : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) s Q) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) s fun u => WP isa (VG.Impl.Rsa.X86.Keys.seqs (y :: ys)) u Q := by
  obtain ⟨_, _, e, q⟩ := h
  obtain ⟨_, _, u, _, e₁, e₂⟩ := exec_seqs_append e
  exact ⟨_, u, e₁, _, _, e₂, q⟩

end

open VG.Proof.Rsa.X86.InvBatchRt.Time (view Pre0)

/-- `wordDivQ`'s loop of digit steps after `k` of them: `LoopQ` from the loop's start `u₃`, the rest of
the loop's run (its correctness `Q` and its run on the view), and whether a step follows. -/
def LQ (g : Geo) (ml a x r m t : Nat) (extra : Bool) (Q : State → Prop) (k : Nat) (u : State) : Prop :=
  ∃ u₃ Mn X₀, P0 g u₃ ∧ val32 u₃.mem g.B (arr (kw (16 * g.n + 24)) x) (xn (16 * g.n + 24) extra) = X₀ ∧
    val32 u₃.mem g.B (arr (kw (16 * g.n + 24)) m) (wq a) = Mn ∧ StepHdr u₃.mem g.B Mn (wq a) ∧
    LoopQ u₃ g.B g.Z (16 * g.n + 24) 22 ml a x r t Mn X₀ (xn (16 * g.n + 24) extra - wq a + 1) k u ∧
    (k < xn (16 * g.n + 24) extra - wq a + 1 →
      WP isa (.loop (VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t) .ne) u Q ∧
      ∃ tr z, Exec isa (.loop (VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t) .ne) (view u g.B g.Z) tr z) ∧
    (xn (16 * g.n + 24) extra - wq a + 1 ≤ k → Q u) ∧
    (0 < k → isa.eval .ne u = some (decide (k < xn (16 * g.n + 24) extra - wq a + 1)))

theorem LQ.p0 {g : Geo} {ml a x r m t : Nat} {extra : Bool} {Q : State → Prop} {k : Nat} {u : State}
    (hx : x < 22) (hr : r < 22) (ht : t < 22) (h : LQ g ml a x r m t extra Q k u) : P0 g u := by
  obtain ⟨u₃, _, _, p, _, _, _, I, _⟩ := h
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound p.1.lenLe
  exact p.keep I.rest (by decide) (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside p.1.ws I.keep (by simp; omega_using [hx, hr, ht]) (by decide))

/-- `wordDivQ`, related: from states that run it (`Q`) on themselves and on their views. -/
theorem relWordDivQ {g : Geo} {ml a x r m t : Nat} {extra : Bool} {Pst Q : State → Prop}
    (hx : x < 22) (hr : r < 22) (hmN : m < 22) (ht : t < 22)
    (hrt : r ≠ t) (hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw (16 * g.n + 24))
    (hP0 : ∀ s, Pst s → P0 g s) (hm : ∀ s, Pst s → MLen s g.B g.Z ml a)
    (hwp : ∀ s, Pst s → WP isa (VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ ml x r m t extra) s Q)
    (hrv : ∀ s, Pst s → ∃ tr z, Exec isa (VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ ml x r m t extra)
      (view s g.B g.Z) tr z)
    (cpre : OkK [] (VG.Impl.Rsa.X86.Keys.seqs (wdqPre ml x r m extra)))
    (cA : OkK [oSteps] (VG.Impl.Rsa.X86.Keys.seqs (dqA ml x r m t))) (c3 : OkK [oSteps] (dq3 x))
    (c4 : OkK [oSteps] dq4) :
    RelCT isa (Both Pst) (VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ ml x r m t extra) (Both Q) := by
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = xn (16 * g.n + 24) extra - wq a + 1 := ⟨_, rfl⟩
  have xnb : kw (16 * g.n + 24) ≤ xn (16 * g.n + 24) extra ∧ xn (16 * g.n + 24) extra ≤ kw (16 * g.n + 24) + 1 := by
    cases extra <;> simp [xn]
  have hds : ∀ d ∈ [oSteps], d + 4 ≤ 160 := by decide
  have wr : ∀ s, P0 g s → (⟨g.B, g.Z⟩ : Region) ∈ s.wr := fun s p => p.1.ws.workspace.wr
  rw [wordDivQ_eq] at hwp hrv ⊢
  refine relSeqs (R := Both (LQ g ml a x r m t extra Q 0))
    ((leafK (P := Pst) (Q := LQ g ml a x r m t extra Q 0) (fun _ => 0) (by simp) hP0 (by simp)
      (fun s h => run_app_left (hrv s h)) (fun s h => ?_) cpre).mono (fun _ _ h => h) fun _ _ h => h) ?_
  · have W1 := wdqPre_ok (hP0 s h).1 (hm s h) hx hr hmN ht hrt hmt hrm hxr hxt hxm h4 hw (t := t) (extra := extra)
    have W2 := wp_seqs_app (hwp s h)
    have W3 := wp_viewRunApp (F := fun _ => True) (wr s (hP0 s h)) (WP.mono W1 fun _ _ => trivial) (hrv s h)
    refine WP.mono (WP.and W1 (WP.and W2 W3)) fun u ⟨⟨Mn, X₀, X₃, M₃, H₃, I₀, O, K⟩, w2, _, w3⟩ => ?_
    exact ⟨u, Mn, X₀, (hP0 s h).keep K (by decide) (by decide) O, X₃, M₃, H₃, I₀, fun _ => ⟨w2, w3⟩,
      fun h => absurd h (by omega_using []), fun h => absurd h (Nat.lt_irrefl 0)⟩
  refine (relLoopB (LQ g ml a x r m t extra Q) (K := Sc) (by omega_using [hSc]) (fun k hk => ?_)
    (fun k s hk _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, f⟩ := h; rw [hSc]; exact f hk)).mono
    (fun _ _ h => h) fun s t ⟨hs, ht⟩ => by
      obtain ⟨_, _, _, _, _, _, _, _, _, es, _⟩ := hs
      obtain ⟨_, _, _, _, _, _, _, _, _, et, _⟩ := ht
      exact ⟨es (by omega_using [hSc]), et (by omega_using [hSc])⟩
  -- One digit step: three leaves.
  let MA : State → Prop := fun v => P0 g v ∧ w32 v.mem g.B oSteps = Sc - k ∧
    WP isa (VG.Impl.Rsa.X86.Keys.seqs [dq3 x, dq4]) v (LQ g ml a x r m t extra Q (k + 1)) ∧
    ∃ tr z, Exec isa (VG.Impl.Rsa.X86.Keys.seqs [dq3 x, dq4]) (view v g.B g.Z) tr z
  let MB : State → Prop := fun w => P0 g w ∧ w32 w.mem g.B oSteps = Sc - k ∧
    WP isa dq4 w (LQ g ml a x r m t extra Q (k + 1)) ∧ ∃ tr z, Exec isa dq4 (view w g.B g.Z) tr z
  rw [digitStepQ_eq]
  refine relSeqs (R := Both MA)
    ((leafK (P := LQ g ml a x r m t extra Q k) (Q := MA) (fun _ => Sc - k) hds (fun s h => h.p0 hx hr ht)
      (fun s h d hd => ?_) (fun s h => ?_) (fun u h => ?_) cA).mono (fun _ _ h => h) fun _ _ h => h)
    (VG.RelCT.seq (R := Both MB)
      ((leafK (P := MA) (Q := MB) (fun _ => Sc - k) hds (fun s h => h.1)
        (fun s h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact h.2.1)
        (fun s h => run_seq_left h.2.2.2) (fun v h => ?_) c3).mono (fun _ _ h => h) fun _ _ h => h)
      ((leafK (P := MB) (Q := LQ g ml a x r m t extra Q (k + 1)) (fun _ => Sc - k) hds (fun s h => h.1)
        (fun s h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact h.2.1)
        (fun s h => h.2.2.2) (fun w h => h.2.2.1) c4).mono (fun _ _ h => h) fun _ _ h => h))
  · simp only [List.mem_singleton] at hd; subst hd
    obtain ⟨_, _, _, _, _, _, _, I, _⟩ := h
    rw [hSc]; exact I.steps
  · obtain ⟨_, _, _, _, _, _, _, _, c, _⟩ := h
    have r := run_loop_body (c (by omega_using [hSc, hk])).2
    rw [digitStepQ_eq] at r
    exact run_app_left r
  · have pu : P0 g u := h.p0 hx hr ht
    obtain ⟨u₃, Mn, X₀, p₃, X₃, M₃, H₃, I, c, _⟩ := h
    obtain ⟨cw, cr⟩ := c (by omega_using [hSc, hk])
    have D := digitStepQ_ok hx hr hmN ht hrt hmt hrm hxr hxt hxm h4 hw X₃ M₃ H₃ rfl (by omega_using [hSc, hk]) I
    have step : WP isa (VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t) u
        (LQ g ml a x r m t extra Q (k + 1)) := by
      refine WP.mono (WP.and D (WP.and (wp_loop_cont cw) (wp_viewRunLoop (F := fun _ => True) (wr u pu)
        (WP.mono D fun _ _ => trivial) cr))) fun w ⟨⟨I', z⟩, ⟨c1, c2⟩, _, c3⟩ => ?_
      have ev : isa.eval .ne w = some (decide (k + 1 < xn (16 * g.n + 24) extra - wq a + 1)) := by
        show w.zf.map (!·) = _
        rw [z]
        simp only [Option.map_some]
        congr 1
        by_cases e : k + 1 = xn (16 * g.n + 24) extra - wq a + 1
        · rw [decide_eq_true e, decide_eq_false (by omega_using [e])]; rfl
        · rw [decide_eq_false e, decide_eq_true (by omega_using [hSc, hk, e])]; rfl
      refine ⟨u₃, Mn, X₀, p₃, X₃, M₃, H₃, I', fun hk1 => ⟨c1 (by rw [ev]; simp [hk1]),
        c3 (by rw [ev]; simp [hk1])⟩, fun hk1 => c2 (by rw [ev]; simp; omega_using [hk1]), fun _ => ev⟩
    rw [digitStepQ_eq] at step D cr
    have rb := run_loop_body cr
    have W2 := wp_seqs_app step
    have W3 := wp_viewRunApp (F := fun _ => True) (wr u pu) (WP.mono W2 fun _ _ => trivial) rb
    have W1 := dsA_ok hx hr hmN ht hrt hmt hrm hxr hxt hxm h4 hw X₃ M₃ H₃ rfl (by omega_using [hSc, hk]) I
    refine WP.mono (WP.and W1 (WP.and W2 W3)) fun v ⟨⟨hv, O, K, st⟩, w2, _, w3⟩ => ?_
    exact ⟨pu.keep K (by decide) (by decide) O, by rw [hSc]; exact st, w2, w3⟩
  · obtain ⟨pv, st, cw, cr⟩ := h
    have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound pv.1.lenLe
    have W1 := dsB_ok pv.1 hx st (by omega_using [hk]) (by omega_using [hSc, xnb])
    have W2 := WP.seq_iff.mp cw
    have W3 := wp_viewRun (F := fun _ => True) (wr v pv) (WP.mono W1 fun _ _ => trivial) cr
    refine WP.mono (WP.and W1 (WP.and W2 W3)) fun w ⟨⟨_, O, K, st'⟩, w2, _, w3⟩ => ?_
    exact ⟨pv.keep K (by decide) (by decide) O, st', w2, w3⟩

end VG.Proof.Rsa.X86.Recover
