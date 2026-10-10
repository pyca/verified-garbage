import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-!
# RSA private keys on x86-64: the division

`divStep`, one step of `divmod`, is `VG.Proof.Rsa.divStep` on the arrays
(`divStepCode_ok`): the remainder `R` (`w + 1` words) and the register `Q`
(`w` words), while `R` is below the divisor; `divmod` is `KeyMath.divIter`
for `64 w` steps from `(0, Q)` (`divmod_ok`): the remainder and the
quotient (`divIter_done`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem mask_add_one (c : Bool) : (mask c + 1).toNat = if c then 0 else 1 := by cases c <;> decide

/-- An even word plus a bit does not carry. -/
theorem add_bit {x r : BitVec 64} (hx : x.toNat % 2 = 0) (hr : r.toNat ≤ 1) : (x + r).toNat = x.toNat + r.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := x.isLt; omega_using [hx, hr])]

/-- `2 Q`'s carry out of `K` bits is `Q`'s top bit. -/
theorem two_mul_div {Q K : Nat} (hK : 1 ≤ K) : 2 * Q / 2 ^ K = Q / 2 ^ (K - 1) := by
  rw [show 2 ^ K = 2 * 2 ^ (K - 1) by rw [← Nat.pow_succ']; congr 1; omega_using [hK], Nat.mul_div_mul_left _ _ (by decide)]

/-- A shift left of `[q]` (`w` words) into `[r]` (`w + 1` words). -/
theorem divShift_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hQ : iQ < 16) (hR : iR < 16) (hQR : iQ ≠ iR) :
    WP isa (seqs (divShiftP iQ iR)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧
      wv t.mem B (slot w iQ) w = 2 * wv s.mem B (slot w iQ) w % 2 ^ (64 * w) ∧
      (wv s.mem B (slot w iR) (w + 1) < 2 ^ (64 * w) →
        wv t.mem B (slot w iR) (w + 1) =
          2 * wv s.mem B (slot w iR) (w + 1) + wv s.mem B (slot w iQ) w / 2 ^ (64 * w - 1)) ∧
      Frm B [ar w iQ, ar w iR] s.mem t.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sp := slot_sep (w := w) hQR
  simp only [divShiftP, seqs]
  -- `rbp := 0` and `rbx := Q`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧
    t.mem = s.mem) (by xrun) rfl)
    fun s₀ ⟨⟨hbp₀, m₀⟩, k₀⟩ => WP.mono (base_ok iQ (r := .rbx) (by decide) ((k₀.gpr (by decide)).trans hdi)
      ((k₀.gpr (by decide)).trans h9)) fun s₁ ⟨hbx₁, m₁, k₁⟩ => ?_))
  have k01 := k₀.trans k₁
  -- `Q := 2 Q`.
  refine WP.seq (WP.mono (shl_ok (hs.congr k01.2.2) hbx₁ ((k01.gpr (by decide)).trans h12)
    ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega_using [hw]) (by omega_using [sQ])) fun s₂ ⟨c₁, hc₁, hv₂, ho₂, k₂⟩ => ?_)
  have k02 := k01.trans k₂
  rw [m₁, m₀] at hv₂ ho₂
  simp only [Bool.toNat_false, Nat.add_zero] at hv₂
  -- `rbx := R`, `r12 := w + 1`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iR (r := .rbx) (by decide) ((k02.gpr (by decide)).trans hdi)
      ((k02.gpr (by decide)).trans h9)) fun s₃ ⟨hbx₃, m₃, k₃⟩ => WP.mono (WP.keep [.r12]
      (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ t.mem = s₃.mem ∧
        t.gpr .rbp = s₃.gpr .rbp) (by
        xrun [(k₃.gpr (by decide) : s₃.gpr .r12 = _), (k02.gpr (by decide) : s₂.gpr .r12 = _), h12]
        exact ofNat_add_one w) rfl)
    fun s₄ ⟨⟨h12₄, m₄, hbp₄⟩, k₄⟩ => ?_))
  have k04 := (k02.trans k₃).trans k₄
  -- `R := 2 R + c₁`.
  refine WP.mono (shl_ok (c₀ := c₁) (hs.congr k04.2.2) ((k₄.gpr (by decide)).trans hbx₃) h12₄
    (by rw [hbp₄, (k₃.gpr (by decide) : s₃.gpr .rbp = _)]; exact hc₁) (by omega_using []) (by omega_using [hw]) (by omega_using [sR]))
    fun t ⟨c₂, _, hv, ho, k₅⟩ => ?_
  rw [m₄, m₃] at hv ho
  have hQ' : wv t.mem B (slot w iQ) w = wv s₂.mem B (slot w iQ) w :=
    ho.wv (by omega_using [sp]) (by omega_using [hn, sQ])
  have hR' : wv s₂.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iR) (w + 1) :=
    ho₂.wv (by omega_using [sp]) (by omega_arith)
  have hQlt := wv_lt s₂.mem B (slot w iQ) w
  have hQs := wv_lt s.mem B (slot w iQ) w
  have hc1 : c₁.toNat = wv s.mem B (slot w iQ) w / 2 ^ (64 * w - 1) := by
    rw [← two_mul_div (by omega_using [hw1]), ← hv₂, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hQlt]
    simp
  refine ⟨(k₅.gpr (by decide)).trans h12₄, ?_, fun hRlt => ?_, ?_, ((k04.trans k₅).mono (by decide))⟩
  · rw [hQ', ← hv₂, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQlt]
  · rw [hR'] at hv
    have hc1' : c₁.toNat ≤ 1 := Bool.toNat_le _
    have : 2 * wv s.mem B (slot w iR) (w + 1) + c₁.toNat < 2 ^ (64 * (w + 1)) := by
      rw [show 64 * (w + 1) = 64 * w + 64 by omega_using [], Nat.pow_add]
      have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
      omega_using [hRlt, hc1']
    have hc2 : c₂.toNat = 0 := by
      rcases Bool.toNat_le c₂ |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h | h
      · exact h
      · rw [h] at hv; omega_arith
    rw [hc2] at hv
    omega_using [hv, hc1]
  · intro x hx
    have a := hx (ar w iQ) (by simp)
    have b := hx (ar w iR) (by simp)
    rw [ho x (by dsimp only at b; omega_using [b]), ho₂ x (by dsimp only at a; omega_using [a])]

theorem sx0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

theorem ofNat_succ_sub_one (w : Nat) : BitVec.ofNat 64 (w + 1) - 1 = BitVec.ofNat 64 w := by
  rw [← ofNat_add_one, BitVec.add_sub_cancel]

/-- Three bases. -/
theorem base3_ok {s : State} {B : Addr} {w : Nat} (i j k : Nat) {r₁ r₂ r₃ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₃ : r₃ ≠ .r9) (h₁₂ : r₂ ≠ r₁) (h₁₃ : r₃ ≠ r₁) (h₂₃ : r₃ ≠ r₂) (hdi : s.gpr .rdi = B)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) (hr2 : r₂ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ (base j r₂ ++ base k r₃))) s fun t =>
      t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.gpr r₃ = off B (slot w k) ∧ t.mem = s.mem ∧
        Keep [r₁, r₂, r₃] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t₂ ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t₂.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  refine WP.mono (base_ok k h₃ ((g2 _ (Ne.symm hr2)).trans ((g1 _ (Ne.symm hr1)).trans hdi))
    ((g2 _ (Ne.symm h₂)).trans ((g1 _ (Ne.symm h₁)).trans h9))) fun t ⟨e₃, m₃, k₃⟩ => ?_
  have g3 : ∀ r, r ≠ r₃ → t.gpr r = t₂.gpr r := fun r h => k₃.gpr (by simp [h])
  refine ⟨(g3 _ (Ne.symm h₁₃)).trans ((g2 _ (Ne.symm h₁₂)).trans e₁), (g3 _ (Ne.symm h₂₃)).trans e₂, e₃,
    m₃.trans (m₂.trans m₁), ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The subtraction of the divisor and the selection: `[r] := [r] - [d]` if
it does not borrow (`b`), over `w + 1` words. -/
theorem divSub_ok {s : State} {B : Addr} {Z w : Nat} {iR iD iT : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (w + 1)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (seqs (divSubP iR iD iT)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧
      t.gpr .rbp = mask (decide (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w)) ∧
      wv t.mem B (slot w iR) (w + 1) = (if wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w then
        wv s.mem B (slot w iR) (w + 1) else wv s.mem B (slot w iR) (w + 1) - wv s.mem B (slot w iD) w) ∧
      Frm B [ar w iR, ar w iT] s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r8, .r10, .rsi, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have pRD := slot_sep (w := w) dRD
  have pRT := slot_sep (w := w) dRT
  have pDT := slot_sep (w := w) dDT
  simp only [divSubP, seqs, List.append_assoc]
  -- `r12 := w`, `rbp := 0`, the bases.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r12, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by xrun [h12, ofNat_succ_sub_one]) rfl)
    fun s₀ ⟨⟨h12₀, hbp₀, m₀⟩, k₀⟩ => ?_))
  refine WP.mono (base3_ok iR iD iT (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k₀.gpr (by decide)).trans hdi) ((k₀.gpr (by decide)).trans h9)
    (by decide) (by decide)) fun s₁ ⟨h8, h10, hsi, m₁, k₁⟩ => ?_
  have k01 := k₀.trans k₁
  -- `T := R - D` over `w` words.
  refine WP.seq (WP.mono (sub_ok (hs.congr k01.2.2) h8 h10 hsi ((k₁.gpr (by decide)).trans h12₀)
    ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega_using [hw]) (by omega_using [sR]) (by omega_using [sD])
        (by omega_using [sT]) (by omega_using [pRT]) (by omega_using [pDT]))
    fun s₂ ⟨b₁, hb₁, hv₂, ho₂, k₂⟩ => ?_)
  rw [m₁, m₀] at hv₂ ho₂
  have k02 := k01.trans k₂
  have hs₂ := hs.congr k02.2.2
  have hR₂ : word s₂.mem B (slot w iR + 8 * w) = word s.mem B (slot w iR + 8 * w) := ho₂.word (by omega_using [pRT])
      (by omega_using [hn, sR])
  -- The top word: `T_w := R_w - b₁`, and `rbp` its borrow.
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .r12] (Q := fun t =>
      ∃ b₂ : Bool, t.gpr .rbp = mask b₂ ∧ t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ ∃ r : BitVec 64,
        t.mem = s₂.mem.writeW (off B (slot w iT + 8 * w)) r ∧
        r.toNat + 0 + b₁.toNat = (word s.mem B (slot w iR + 8 * w)).toNat + 2 ^ 64 * b₂.toNat) (by
      unfold cfFromRbp cfToRbp
      have e8 : s₂.gpr .r8 = off B (slot w iR) := (k₂.gpr (by decide)).trans h8
      have esi : s₂.gpr .rsi = off B (slot w iT) := (k₂.gpr (by decide)).trans hsi
      have e12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12₀)
      xrun [State.ea, ix, e8, esi, e12, addr0 (b := off B (slot w iR)) rfl rfl,
        addr0 (b := off B (slot w iT)) rfl rfl, hb₁, cf_mask, hs₂.ld (show slot w iR + 8 * w + 8 ≤ Z by omega_using [sR]),
        hs₂.st (show slot w iT + 8 * w + 8 ≤ Z by omega_using [sT]), hR₂, ofNat_add_one, e12, sx0]
      refine ⟨_, rfl, _, rfl, ?_⟩
      have := sbb_toNat (Bignum.word s.mem B (slot w iR + 8 * w)) 0 b₁
      simpa using this) rfl) fun s₃ ⟨⟨b₂, hb₂, h12₃, r, m₃, hr⟩, k₃⟩ => ?_)
  have k03 := k02.trans k₃
  -- The value of `T` over `w + 1` words.
  have hT : wv s₃.mem B (slot w iT) (w + 1) + wv s.mem B (slot w iD) w =
      wv s.mem B (slot w iR) (w + 1) + 2 ^ (64 * (w + 1)) * b₂.toNat := by
    rw [m₃, wv_writeW_top _ _ _ _ _ (by omega_using [hn, sT]), wv, pow64_succ]
    simp only [Bignum.word] at hr ⊢
    grind
  have hb : b₂ = decide (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w) :=
    lt_of_borrow (wv_lt _ _ _ _) hT
  -- The selection.
  have k13 := k₂.trans k₃
  refine WP.mono (sel_ok (hs.congr k03.2.2) ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans hsi)
    hb₂ h12₃ (by omega_using []) (by omega_using [hw]) (by omega_using [sR]) (by omega_using [sT])
        (by omega_using [pRT])) fun t ⟨hv, ho, k₄⟩ => ?_
  have hR₃ : wv s₃.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iR) (w + 1) := by
    rw [m₃, (writeW_outside s₂.mem B r (by omega_using [hn, sT])).wv (by omega_using [pRT]) (by omega_using [hn, sR])]
    exact ho₂.wv (by omega_using [pRT]) (by omega_using [hn, sR])
  refine ⟨(k₄.gpr (by decide)).trans h12₃, (k₄.gpr (by decide)).trans (hb ▸ hb₂), ?_, ?_,
    (k03.trans k₄).mono (by decide)⟩
  · rw [hv, hR₃]
    cases b₂
    · simp only [Bool.false_eq_true, ite_false]
      have : ¬ wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w := by simpa using hb
      simp only [this, ite_false]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hT
      omega_using [hT]
    · have : wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w := by simpa using hb
      simp [this]
  · intro x hx
    have a := hx (ar w iR) (by simp)
    have b := hx (ar w iT) (by simp)
    dsimp only at a b
    rw [ho x (by omega_using [a]), m₃, writeW_outside s₂.mem B r (by omega_using [hn, sT]) x (by omega_using [b]),
        ho₂ x (by omega_using [b])]

/-- A number of `w ≥ 1` words is its low word and the `w - 1` above. -/
theorem wv_low {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  rw [show w = 1 + (w - 1) by omega_using [hw], wv_add, show 1 + (w - 1) - 1 = w - 1 by omega_using []]
  simp [wv]

/-- The quotient's new bit (`rbp` the mask of the borrow `b`) into word 0 of
`[q]`, `r12 := w`, and the step counter. -/
theorem divBit_ok {s : State} {B : Addr} {Z w k : Nat} {iQ : Nat} {b : Bool} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 (w + 1))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hbp : s.gpr .rbp = mask b)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 64 * w) (hZ : slot w 16 ≤ Z) (hQ : iQ < 16)
    (hev : (word s.mem B (slot w iQ)).toNat % 2 = 0) :
    WP isa (.block (divBitP iQ)) s fun t =>
      t.zf = some (decide (k + 1 = 64 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      wv t.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w + (if b then 0 else 1) ∧
      Frm B [ar w iQ] s.mem t.mem ∧ Keep [.rax, .rbx, .rdx, .r12, .r13] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  rw [divBitP, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rax] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      (t.gpr .rax).toNat = (if b then 0 else 1) ∧ t.mem = s.mem) (by
      xrun [h12, hbp, ofNat_succ_sub_one]
      exact mask_add_one b) rfl) fun s₁ ⟨⟨h12₁, hax₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (base_ok iQ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hdi)
    ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have e13 : s₂.gpr .r13 = BitVec.ofNat 64 k := (k12.gpr (by decide)).trans h13
  have e11 : s₂.gpr .r11 = BitVec.ofNat 64 (64 * w) := (k12.gpr (by decide)).trans h11
  have eax : (s₂.gpr .rax).toNat = if b then 0 else 1 := by rw [(k₂.gpr (by decide) : s₂.gpr .rax = _)]; exact hax₁
  have hw0 : word s₂.mem B (slot w iQ) = word s.mem B (slot w iQ) := by rw [m₂, m₁]
  refine WP.mono (WP.keep [.rdx, .r13] (Q := fun t => t.zf = some (decide (k + 1 = 64 * w)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.mem = s₂.mem.writeW (off B (slot w iQ)) (word s.mem B (slot w iQ) + s₂.gpr .rax)) (by
      xrun [State.ea, at0, hbx, e13, e11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot w iQ) (by omega_using [sQ]), hs₂.st (d := slot w iQ) (by omega_using [sQ]), hw0, ofNat_add_one,
        ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega_using [hw, hk]) (show 64 * w < 2 ^ 64 by omega_using [hw])]) rfl)
    fun t ⟨⟨hz, h13t, mt⟩, k₃⟩ => ?_
  have hax : (s₂.gpr .rax).toNat ≤ 1 := by rw [eax]; split <;> omega_using []
  refine ⟨hz, h13t, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁), ?_, ?_,
    (k12.trans k₃).mono (by decide)⟩
  · rw [mt, wv_low hw1, wv_low (m := s.mem) hw1, word_writeW_self, add_bit hev hax, eax,
      (writeW_outside s₂.mem B _ (by omega_using [hn, sQ])).wv (Or.inr (by omega_using [])) (by omega_using [hn, sQ]), m₂, m₁]
    omega_using []
  · intro x hx
    have a := hx (ar w iQ) (by simp)
    dsimp only at a
    rw [mt, writeW_outside s₂.mem B _ (by omega_using [hn, sQ]) x (by omega_using [a]), m₂, m₁]

/-- The registers `divStep` and `inverse`'s step may change. -/
def stepRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r13, .r14, .r15]

/-- One step of `divmod`: `VG.Proof.Rsa.divStep` while the remainder is below the
divisor. -/
theorem divStepCode_ok {s : State} {B : Addr} {Z w k : Nat} {iQ iR iD iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 64 * w) (hZ : slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) s fun t =>
      t.zf = some (decide (k + 1 = 64 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧ Keep stepRegs s t ∧
      (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w →
        (wv t.mem B (slot w iR) (w + 1), wv t.mem B (slot w iQ) w) =
          VG.Proof.Rsa.divStep (wv s.mem B (slot w iD) w) (64 * w)
            (wv s.mem B (slot w iR) (w + 1), wv s.mem B (slot w iQ) w)) := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have pQR := slot_sep (w := w) dQR
  have pQD := slot_sep (w := w) dQD
  have pQT := slot_sep (w := w) dQT
  have pRD := slot_sep (w := w) dRD
  have pRT := slot_sep (w := w) dRT
  rw [VG.Impl.Rsa.X86_64.Keys.divStep]
  refine wp_seqs_append (by simp [divShiftP]) (by simp) (WP.mono (divShift_ok hs hdi h12 h9 hw1 hw hZ hQ hR dQR)
    fun s₁ ⟨h12₁, hQ₁, hR₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [divSubP]) (by simp) (WP.mono (divSub_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi)
    h12₁ ((k₁.gpr (by decide)).trans h9) hw1 hw hZ hR hD hT dRD dRT (by omega_using [dDT])) fun s₂ ⟨h12₂, hbp₂, hR₂, f₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hD₁ : wv s₁.mem B (slot w iD) w = wv s.mem B (slot w iD) w :=
    f₁.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega_using [pQD, pRD]) (by omega_using [hn, sD])
  have hQ₂ : wv s₂.mem B (slot w iQ) w = wv s₁.mem B (slot w iQ) w :=
    f₂.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega_using [pQR, pQT]) (by omega_using [hn, sQ])
  have hQ2' : wv s₂.mem B (slot w iQ) w = 2 * wv s.mem B (slot w iQ) w % 2 ^ (64 * w) := hQ₂.trans hQ₁
  have hev : (word s₂.mem B (slot w iQ)).toNat % 2 = 0 := by
    have d1 : 2 ∣ 2 ^ (64 * w) := ⟨2 ^ (64 * w - 1), by rw [← Nat.pow_succ']; congr 1; omega_using [hk]⟩
    rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), hQ2', Nat.mod_mod_of_dvd _ d1]
    omega_using []
  simp only [seqs]
  refine WP.mono (divBit_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi) h12₂ ((k12.gpr (by decide)).trans h9)
    hbp₂ ((k12.gpr (by decide)).trans h13) ((k12.gpr (by decide)).trans h11) hw1 hw hk hZ hQ hev)
    fun t ⟨hz, h13t, h12t, hQt, f₃, k₃⟩ => ⟨hz, h13t, h12t, ?_, (k12.trans k₃).mono (by decide), fun hlt => ?_⟩
  · intro x hx
    have a := hx (ar w iQ) (by simp)
    have b := hx (ar w iR) (by simp)
    have c := hx (ar w iT) (by simp)
    rw [f₃ x (by simpa using a), f₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
      <;> with_reducible assumption), f₁ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
      <;> with_reducible assumption)]
  · have hRlt : wv s.mem B (slot w iR) (w + 1) < 2 ^ (64 * w) := Nat.lt_trans hlt (wv_lt _ _ _ _)
    have hR₁' := hR₁ hRlt
    have hRt : wv t.mem B (slot w iR) (w + 1) = wv s₂.mem B (slot w iR) (w + 1) :=
      f₃.wv_eq (fun r hr => by simp at hr; subst hr; dsimp only; omega_using [pQR]) (by omega_using [hn, sR])
    simp only [VG.Proof.Rsa.divStep]
    rw [hQt, hQ2', hRt, hR₂, hD₁, hR₁']
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]

theorem ofNat_dbl (a : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 a = BitVec.ofNat 64 (2 * a) := by
  rw [← BitVec.ofNat_add, Nat.two_mul]

/-- The invariant of `divmod`'s loop after `j` steps from `s`, for the
dividend `N` and the divisor `D`. -/
structure DivInv (s : State) (B : Addr) (Z w iQ iR iD iT N D : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r9 : t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (64 * w)
  frm : Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem
  keep : Keep (.r9 :: .r11 :: stepRegs) s t
  val : 0 < D → (wv t.mem B (slot w iR) (w + 1), wv t.mem B (slot w iQ) w) = divIter D (64 * w) j (0, N)

/-- `divmod`: the remainder of `[q]` by `[d]` into `[r]` (`w + 1` words) and
the quotient into `[q]`, if `[d]` is not zero. -/
theorem divmod_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR iD iT : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t =>
      t.gpr .rdi = B ∧ Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧ Keep (.r9 :: .r11 :: stepRegs) s t ∧
      (0 < wv s.mem B (slot w iD) w →
        wv t.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iQ) w % wv s.mem B (slot w iD) w ∧
        wv t.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w / wv s.mem B (slot w iD) w) := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have pQR := slot_sep (w := w) dQR
  have pRD := slot_sep (w := w) dRD
  have pRT := slot_sep (w := w) dRT
  have pQD := slot_sep (w := w) dQD
  have pDT := slot_sep (w := w) dDT
  have h256 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 16 (show 31 < 32 by decide); omega_using [hZ, this]
  unfold divmod
  simp only [seqs]
  -- The registers.
  have e₁ : WP isa (.block (divInit iR)) s fun (t : State) =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r8 = off B (slot w iR) ∧
      t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .r11, .r13] s t := by
    rw [divInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ws_ok hs hdi h256 hW hS) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    refine WP.mono (base_ok iR (r := .r8) (by decide) ((k₁.gpr (by decide)).trans hdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have e12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem)
      (by xrun [e12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.mem = s₃.mem)
      (by
        xrun [h11, ofNat_dbl, List.replicate]
        congr 1; omega_using []) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
      (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
    have kk := (((k12.trans k₃).trans k₄).trans k₅)
    refine ⟨(kk.gpr (by decide)).trans hdi, (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h12,
      (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h9, ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h8,
      (k₅.gpr (by decide)).trans h11', h13, by rw [m₅, m₄, m₃, m₂, m₁], kk.mono (by decide)⟩
  refine WP.seq (WP.mono e₁ fun s₁ ⟨hdi₁, h12₁, h9₁, h8₁, h11₁, h13₁, m₁, k₁⟩ => ?_)
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8₁ h12₁ hw1 (by omega_using [hw]) (by omega_using [sR]))
      fun s₂ ⟨hz, ho, k₂⟩ => ?_)
  rw [m₁] at ho
  have k12 := k₁.trans k₂
  have hN₂ : wv s₂.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w := ho.wv (by omega_using [pQR]) (by omega_using [hn, sQ])
  have hD₂ : wv s₂.mem B (slot w iD) w = wv s.mem B (slot w iD) w := ho.wv (by omega_using [pRD]) (by omega_using [hn, sD])
  have hR₂ : wv s₂.mem B (slot w iR) (w + 1) = 0 := by
    have := wv_add s₂.mem B (slot w iR) (w + 1) 1
    rw [show w + 1 + 1 = w + 2 by omega_using [], hz] at this
    omega_using [this]
  -- The loop.
  refine wp_upto (a := 0) (N := 64 * w) (by omega_using [hw1])
    (DivInv s B Z w iQ iR iD iT (wv s.mem B (slot w iQ) w) (wv s.mem B (slot w iD) w))
    (fun j _ hj t hI => ?_) (fun t hI => ⟨hI.rdi, hI.frm, hI.keep, fun hD0 => ?_⟩)
    ⟨hs.congr k12.2.2, (k₂.gpr (by decide)).trans hdi₁, (k₂.gpr (by decide)).trans h12₁,
      (k₂.gpr (by decide)).trans h9₁, (k₂.gpr (by decide)).trans h13₁, (k₂.gpr (by decide)).trans h11₁,
      Frm.of_outside (ho.mono (Nat.le_refl _) (Nat.le_refl _)) (by simp), k12.mono (by decide),
      fun _ => by rw [hR₂, hN₂]; rfl⟩
  · have hDt : wv t.mem B (slot w iD) w = wv s.mem B (slot w iD) w :=
      hI.frm.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [pQD, pRD, pDT]) (by omega_using [hn, sD])
    refine WP.mono (divStepCode_ok hI.scr hI.rdi hI.r12 hI.r9 hI.r13 hI.r11 hw1 hw hj hZ hQ hR hD hT dQR dQD dQT dRD
      dRT dDT) fun t' ⟨hz', h13', h12', f', k', hv'⟩ => ⟨hz', ?_⟩
    refine ⟨hI.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI.rdi, h12', (k'.gpr (by decide)).trans hI.r9, h13',
      (k'.gpr (by decide)).trans hI.r11, hI.frm.trans f', (hI.keep.trans k').mono (by decide), fun hD0 => ?_⟩
    obtain ⟨q, hlt, -, -, -⟩ := divIter_inv hD0 (wv_lt s.mem B (slot w iQ) w) j (by omega_using [hj])
    have hv := hI.val hD0
    have hRt : wv t.mem B (slot w iR) (w + 1) < wv t.mem B (slot w iD) w := by
      rw [hDt, show wv t.mem B (slot w iR) (w + 1) = _ from congrArg Prod.fst hv]; exact hlt
    rw [hv' hRt, hDt, hv]
    rfl
  · have := hI.val hD0
    rw [divIter_done hD0 (wv_lt s.mem B (slot w iQ) w), Prod.ext_iff] at this
    exact this

end VG.Proof.Rsa.X86_64
