module

import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `Rsa.X86_64.Inv`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.Div`, which this module and modules that import it used -/

section

/-!
# RSA private keys on x86-64: the division

`divStep`, one step of `divmod`, is `VG.Proof.Rsa.divStep` on the arrays
(`divStepCode_ok`): the remainder `R` (`w + 1` words) and the register `Q`
(`w` words), while `R` is below the divisor; `divmod` is `KeyMath.divIter`
for `64 w` steps from `(0, Q)` (`divmod_ok`): the remainder and the
quotient (`divIter_done`).
-/

@[expose] public section

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
  obtain sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  obtain sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  obtain sp := slot_sep (w := w) hQR
  simp only [divShiftP, seqs]
  -- `rbp := 0` and `rbx := Q`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧
    t.mem = s.mem) (by xrun) rfl)
    fun s₀ ⟨⟨hbp₀, m₀⟩, k₀⟩ => WP.mono (base_ok iQ (r := .rbx) (by decide) ((k₀.gpr (by decide)).trans hdi)
      ((k₀.gpr (by decide)).trans h9)) fun s₁ ⟨hbx₁, m₁, k₁⟩ => ?_))
  obtain k01 := k₀.trans k₁
  -- `Q := 2 Q`.
  refine WP.seq (WP.mono (shl_ok (hs.congr k01.2.2) hbx₁ ((k01.gpr (by decide)).trans h12)
    ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega_using [hw]) (by omega_using [sQ])) fun s₂ ⟨c₁, hc₁, hv₂, ho₂, k₂⟩ => ?_)
  obtain k02 := k01.trans k₂
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
  obtain k04 := (k02.trans k₃).trans k₄
  -- `R := 2 R + c₁`.
  refine WP.mono (shl_ok (c₀ := c₁) (hs.congr k04.2.2) ((k₄.gpr (by decide)).trans hbx₃) h12₄
    (by rw [hbp₄, (k₃.gpr (by decide) : s₃.gpr .rbp = _)]; exact hc₁) (by omega_using []) (by omega_using [hw]) (by omega_using [sR]))
    fun t ⟨c₂, _, hv, ho, k₅⟩ => ?_
  rw [m₄, m₃] at hv ho
  obtain hQ' : wv t.mem B (slot w iQ) w = wv s₂.mem B (slot w iQ) w :=
    ho.wv (by omega_using [sp]) (by omega_using [hn, sQ])
  obtain hR' : wv s₂.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iR) (w + 1) :=
    ho₂.wv (by omega_using [sp]) (by omega_arith)
  obtain hQlt := wv_lt s₂.mem B (slot w iQ) w
  obtain hQs := wv_lt s.mem B (slot w iQ) w
  obtain hc1 : c₁.toNat = wv s.mem B (slot w iQ) w / 2 ^ (64 * w - 1) := by
    rw [← two_mul_div (by omega_using [hw1]), ← hv₂, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hQlt]
    simp
  refine ⟨(k₅.gpr (by decide)).trans h12₄, ?_, fun hRlt => ?_, ?_, ((k04.trans k₅).mono (by decide))⟩
  · rw [hQ', ← hv₂, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQlt]
  · rw [hR'] at hv
    obtain hc1' : c₁.toNat ≤ 1 := Bool.toNat_le _
    have : 2 * wv s.mem B (slot w iR) (w + 1) + c₁.toNat < 2 ^ (64 * (w + 1)) := by
      rw [show 64 * (w + 1) = 64 * w + 64 by omega_using [], Nat.pow_add]
      have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
      omega_using [hRlt, hc1']
    obtain hc2 : c₂.toNat = 0 := by
      rcases Bool.toNat_le c₂ |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h | h
      · exact h
      · rw [h] at hv; omega_arith
    rw [hc2] at hv
    omega_using [hv, hc1]
  · intro x hx
    obtain a := hx (ar w iQ) (by simp)
    obtain b := hx (ar w iR) (by simp)
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
  obtain g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t₂ ⟨e₂, m₂, k₂⟩ => ?_
  obtain g2 : ∀ r, r ≠ r₂ → t₂.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  refine WP.mono (base_ok k h₃ ((g2 _ (Ne.symm hr2)).trans ((g1 _ (Ne.symm hr1)).trans hdi))
    ((g2 _ (Ne.symm h₂)).trans ((g1 _ (Ne.symm h₁)).trans h9))) fun t ⟨e₃, m₃, k₃⟩ => ?_
  obtain g3 : ∀ r, r ≠ r₃ → t.gpr r = t₂.gpr r := fun r h => k₃.gpr (by simp [h])
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
  obtain sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  rw [divBitP, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rax] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      (t.gpr .rax).toNat = (if b then 0 else 1) ∧ t.mem = s.mem) (by
      xrun [h12, hbp, ofNat_succ_sub_one]
      exact mask_add_one b) rfl) fun s₁ ⟨⟨h12₁, hax₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (base_ok iQ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hdi)
    ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain hs₂ := hs.congr k12.2.2
  obtain e13 : s₂.gpr .r13 = BitVec.ofNat 64 k := (k12.gpr (by decide)).trans h13
  obtain e11 : s₂.gpr .r11 = BitVec.ofNat 64 (64 * w) := (k12.gpr (by decide)).trans h11
  obtain eax : (s₂.gpr .rax).toNat = if b then 0 else 1 := by rw [(k₂.gpr (by decide) : s₂.gpr .rax = _)]; exact hax₁
  obtain hw0 : word s₂.mem B (slot w iQ) = word s.mem B (slot w iQ) := by rw [m₂, m₁]
  refine WP.mono (WP.keep [.rdx, .r13] (Q := fun t => t.zf = some (decide (k + 1 = 64 * w)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.mem = s₂.mem.writeW (off B (slot w iQ)) (word s.mem B (slot w iQ) + s₂.gpr .rax)) (by
      xrun [State.ea, at0, hbx, e13, e11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot w iQ) (by omega_using [sQ]), hs₂.st (d := slot w iQ) (by omega_using [sQ]), hw0, ofNat_add_one,
        ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega_using [hw, hk]) (show 64 * w < 2 ^ 64 by omega_using [hw])]) rfl)
    fun t ⟨⟨hz, h13t, mt⟩, k₃⟩ => ?_
  obtain hax : (s₂.gpr .rax).toNat ≤ 1 := by rw [eax]; split <;> omega_using []
  refine ⟨hz, h13t, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁), ?_, ?_,
    (k12.trans k₃).mono (by decide)⟩
  · rw [mt, wv_low hw1, wv_low (m := s.mem) hw1, word_writeW_self, add_bit hev hax, eax,
      (writeW_outside s₂.mem B _ (by omega_using [hn, sQ])).wv (Or.inr (by omega_using [])) (by omega_using [hn, sQ]), m₂, m₁]
    omega_using []
  · intro x hx
    obtain a := hx (ar w iQ) (by simp)
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
  obtain sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  obtain sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  obtain sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  obtain sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  obtain pQR := slot_sep (w := w) dQR
  obtain pRD := slot_sep (w := w) dRD
  obtain pRT := slot_sep (w := w) dRT
  obtain pQD := slot_sep (w := w) dQD
  obtain pDT := slot_sep (w := w) dDT
  obtain h256 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 16 (show 31 < 32 by decide); omega_using [hZ, this]
  unfold divmod
  simp only [seqs]
  -- The registers.
  obtain e₁ : WP isa (.block (divInit iR)) s fun (t : State) =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r8 = off B (slot w iR) ∧
      t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .r11, .r13] s t := by
    rw [divInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ws_ok hs hdi h256 hW hS) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    refine WP.mono (base_ok iR (r := .r8) (by decide) ((k₁.gpr (by decide)).trans hdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
    obtain k12 := k₁.trans k₂
    obtain e12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem)
      (by xrun [e12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.mem = s₃.mem)
      (by
        xrun [h11, ofNat_dbl, List.replicate]
        congr 1; omega_using []) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
      (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
    obtain kk := (((k12.trans k₃).trans k₄).trans k₅)
    refine ⟨(kk.gpr (by decide)).trans hdi, (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h12,
      (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h9, ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h8,
      (k₅.gpr (by decide)).trans h11', h13, by rw [m₅, m₄, m₃, m₂, m₁], kk.mono (by decide)⟩
  refine WP.seq (WP.mono e₁ fun s₁ ⟨hdi₁, h12₁, h9₁, h8₁, h11₁, h13₁, m₁, k₁⟩ => ?_)
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8₁ h12₁ hw1 (by omega_using [hw]) (by omega_using [sR]))
      fun s₂ ⟨hz, ho, k₂⟩ => ?_)
  rw [m₁] at ho
  obtain k12 := k₁.trans k₂
  obtain hN₂ : wv s₂.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w := ho.wv (by omega_using [pQR]) (by omega_using [hn, sQ])
  obtain hD₂ : wv s₂.mem B (slot w iD) w = wv s.mem B (slot w iD) w := ho.wv (by omega_using [pRD]) (by omega_using [hn, sD])
  obtain hR₂ : wv s₂.mem B (slot w iR) (w + 1) = 0 := by
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
    obtain hv := hI.val hD0
    obtain hRt : wv t.mem B (slot w iR) (w + 1) < wv t.mem B (slot w iD) w := by
      rw [hDt, show wv t.mem B (slot w iR) (w + 1) = _ from congrArg Prod.fst hv]; exact hlt
    rw [hv' hRt, hDt, hv]
    rfl
  · have := hI.val hD0
    rw [divIter_done hD0 (wv_lt s.mem B (slot w iQ) w), Prod.ext_iff] at this
    exact this

end VG.Proof.Rsa.X86_64

end

end

/-!
# RSA private keys on x86-64: masks, and the arrays' separation and bases

The masks of a conjunction and of a word's low bit (`mask_and'`,
`mask_low`), arrays apart (`slot_far`), and two bases at once (`base2_ok`),
which the key routines' proofs share. The inverse itself is
`InvB/Main.lean`'s `inverse_ok`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mask of a word's low bit. -/
theorem mask_low (x : BitVec 64) : BitVec.setWidth 64 (0 : BitVec 32) - (x &&& 1) =
    mask (decide (x.toNat % 2 = 1)) := by
  have h2 : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_using []
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- Three distinct arrays among sixteen are apart. -/
theorem slot_far {w i j : Nat} (h : i ≠ j) : slot w i + 8 * (w + 2) ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ slot w i :=
  slot_sep h

/-- Two bases. -/
theorem base2_ok {s : State} {B : Addr} {w : Nat} (i j : Nat) {r₁ r₂ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₁₂ : r₂ ≠ r₁) (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ base j r₂)) s fun t =>
      t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.mem = s.mem ∧ Keep [r₁, r₂] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  refine WP.mono (base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  exact ⟨(g2 _ (Ne.symm h₁₂)).trans e₁, e₂, m₂.trans m₁, (k₁.trans k₂).mono (by simp)⟩

end VG.Proof.Rsa.X86_64

end

end

/-!
# RSA private keys on x86-64: the working space and its pieces

`Ws`: the working space `vg_rsa_crt_values` and `vg_rsa_recover_primes_det` set
up, the header giving `w`, the stride and the bases of arrays 0 to 7, and 16
arrays fitting in it; kept by code that changes only arrays and the header
slots `sMask` and `sMo` (`Ws.congr`). The pieces of the functions that load,
clear, copy and store arrays (`zeroA_ok`, `copyA_ok`, `loadA_ok`,
`storeA_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The working space at `B` of `Z` bytes, for `w`-word numbers. -/
structure Ws (s : State) (B : Addr) (Z w : Nat) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  hw : word s.mem B (8 * sW) = BitVec.ofNat 64 w
  hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))
  harr : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot w j)
  hZ : slot w 16 ≤ Z
  w1 : 2 ≤ w
  w2 : w < 2 ^ 24

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat} (h : ∀ k < n, word m B (d + 8 * k) = 0) : wv m B d n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wv, ih fun k hk => h k (by omega_arith), h n (by omega_arith)]; rfl

/-- The ranges the pieces may change: arrays, `sMask` and `sMo`. -/
def Mut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ r = (8 * Impl.Bignum.X86_64.Public.sMask, 8) ∨ r = (8 * sMo, 8)

theorem Mut.ofSlot (w j : Nat) (n : Nat) : Mut (Bignum.slot w j, n) :=
  Or.inl (by unfold Bignum.slot hdrBytes; omega_arith)

theorem Ws.congr {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | rfl | rfl
      · omega
      · simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
      · simp only [sMo, sFn]; omega) (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide)
                                         have := h.hZ; omega)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

theorem Ws.good {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    Good s B Z w (word s.mem B (8 * sMinv)) ∧ slot w 8 ≤ Z :=
  ⟨⟨h.scr, h.rdi, ⟨h.hw, rfl, h.harr⟩⟩, Nat.le_trans (by unfold slot; omega_arith) h.hZ⟩

theorem Ws.h256 {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) : 8 * 32 ≤ Z := by
  have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega_arith

theorem Ws.sl {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) h.hZ

/-- `ws`, from the working space. -/
theorem Ws.ws_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block ws) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        Keep [.r12, .r9] s t :=
  VG.Proof.Rsa.X86_64.ws_ok h.scr h.rdi h.h256 h.hw h.hS

/-! ## Clearing and copying -/

/-- `zeroA j`: `[j] := 0` (`w + 2` words). -/
theorem zeroA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t =>
      wv t.mem B (slot w j) (w + 2) = 0 ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold zeroA
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base_ok j (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_))
  refine WP.mono (zeroAccLoop_ok (h.scr.congr (k₁.trans k₂).2.2) h8 ((k₂.gpr (by decide)).trans h12)
    (by have := h.w1; omega_arith) (by have := h.w2; omega_arith) (by omega_arith)) fun t ⟨hz, o, k₃⟩ => ?_
  rw [m₂, m₁] at o
  exact ⟨hz, o, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `copyA o a`: `[o] := [a]` over `w` words. -/
theorem copyA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
        Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sp := slot_far (w := w) hoa
  unfold copyA
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (copyWords_ok hsi hbx ((k₂.gpr (by decide)).trans h12) (by have := h.w1; omega_arith)
    (by have := h.w2; omega_arith) (by omega_arith) (fun i hi => hs₂.ld (by omega_arith)) (fun i hi => hs₂.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## Bytes -/

/-- `loadA j sPtr sLen`: `[j] := ` the `len` bytes at `p`, most significant
first, over `w` words. -/
theorem loadA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = p) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s B Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      wv t.mem B (slot w j) w = Spec.Rsa.os2ip bs ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rsi, .rcx, .rdx, .rbp] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [loadA, seqs]
  refine WP.seq (WP.mono (zeroA_ok h hj) fun s₁ ⟨hz, o₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w j hi; omega_arith)) (by omega_arith)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = p ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h₁.rdi
          have hs₃ := h₁.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_arith)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hh sPtr hP, hh sLen hL, hp, hl]) rfl)
      fun s₄ ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.2.2
  have hsrc₄ : Src s₄ B Z p bs := hsrc.congrK (fun x hx => by
    rw [m₄, m₃, m₂]; exact o₁ x (Or.inr (by omega_arith))) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ hsi hcx ((k₄.gpr (by decide)).trans hbx) hlen hl1 (by omega_arith) rfl
    (by omega_arith) (fun i hi => hsrc₄.rd i (by omega_arith)) (fun i hi => hsrc₄.val i (by omega_arith))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega_arith); omega_arith))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at o
  refine ⟨?_, fun x hx => by rw [o x (by omega_arith), o₁ x hx], (k14.trans k₅).mono (by decide)⟩
  -- The words above the loaded ones are still zero.
  have hz' : ∀ q < w + 2, word s₁.mem B (slot w j + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e := wv_add t.mem B (slot w j) ((len + 7) / 8) (w - (len + 7) / 8)
  rw [show (len + 7) / 8 + (w - (len + 7) / 8) = w by omega_arith] at e
  rw [e, hv, wv_zero (n := w - (len + 7) / 8) fun q hq => by
      rw [o.word (by omega_arith) (by omega_arith), Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega_arith)]
  simp

/-- `storeA j sPtr sLen sMsk`: the low `⌈len / 8⌉` words of `[j]`, masked by
the slot `sMsk`, as `len` bytes at `out`. -/
theorem storeA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen sMsk len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hM : sMsk < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * sMsk) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen sMsk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ t.wr = s.wr ∧ t.rd = s.rd ∧
      Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [storeA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .r15 = mask c ∧ t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_arith)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ sMsk hM, hp, hl, hm]) rfl)
      fun s₄ ⟨⟨hsi, hcx, h15, m₄⟩, k₄⟩ => ?_)))
  have k24 := (k₂.trans k₃).trans k₄
  refine WP.mono (storeBE_ok (w := (len + 7) / 8) (h.scr.congr k24.2.2) ((k₄.gpr (by decide)).trans hbx) hsi hcx h15
    hl1 (by omega_arith) rfl (by omega_arith) (fun i hi => by rw [k24.2.2]; exact hout i hi) hsep)
    fun t ⟨hb, hx, hwr, hrd, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at hb hx
  exact ⟨hb, hx, hwr.trans k24.2.2, hrd.trans k24.2.1, (k24.trans k₅).mono (by decide)⟩

/-- A number below `2^(64 v)` is its low `v` words. -/
theorem wv_low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w) (h : wv m B e w < 2 ^ (64 * v)) :
    wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega_arith] at e1
  have : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega_arith
  rw [e1, this]; simp

end VG.Proof.Rsa.X86_64
