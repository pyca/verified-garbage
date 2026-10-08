import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs

/-!
# RSA private keys on AArch64: the division

`divStep`, one step of `divmod`, is `VG.Proof.Rsa.divStep` on the arrays
(`divStepCode_ok`): the remainder `R` (`w + 1` words) and the register `Q`
(`w` words), while `R` is below the divisor; `divmod` is `KeyMath.divIter`
for `64 w` steps from `(0, Q)` (`divmod_ok`): the remainder and the
quotient (`divIter_done`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `2 Q`'s carry out of `K` bits is `Q`'s top bit. -/
theorem two_mul_div {Q K : Nat} (hK : 1 ≤ K) : 2 * Q / 2 ^ K = Q / 2 ^ (K - 1) := by
  rw [show 2 ^ K = 2 * 2 ^ (K - 1) by rw [← Nat.pow_succ']; congr 1; omega_arith, Nat.mul_div_mul_left _ _ (by decide)]

/-- A shift left of `[q]` (`w` words) into `[r]` (`w + 1` words). -/
theorem divShift_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hQ : iQ < 16) (hR : iR < 16) (hQR : iQ ≠ iR) :
    WP isa (seqs (divShiftP iQ iR)) s fun t =>
      wv t.mem B (slot w iQ) w = 2 * wv s.mem B (slot w iQ) w % 2 ^ (64 * w) ∧
      (wv s.mem B (slot w iR) (w + 1) < 2 ^ (64 * w) →
        wv t.mem B (slot w iR) (w + 1) =
          2 * wv s.mem B (slot w iR) (w + 1) + wv s.mem B (slot w iQ) w / 2 ^ (64 * w - 1)) ∧
      t.gpr .x7 = 0 ∧ Frm B [ar w iQ, ar w iR] s.mem t.mem ∧ Keep [.x3, .x7, .x14, .x16] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sp := slot_sep (w := w) hQR
  simp only [divShiftP, seqs]
  -- `x7 := 0`, `x14 := w`, the carry clear, `x16 := Q`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s.mem) (by brun [h12])
      (by decide) (by decide) (by decide +kernel))
    fun s₀ ⟨⟨h7₀, h14₀, hc₀, m₀⟩, k₀⟩ => WP.mono (base_ok iQ .x16 ((k₀.gpr .x0 (by decide)).trans h0)
      ((k₀.gpr .x11 (by decide)).trans h11)) fun s₁ ⟨⟨h16₁, m₁, c₁⟩, k₁⟩ => ?_))
  have k01 := k₀.trans k₁
  -- `Q := 2 Q`.
  refine WP.seq (WP.mono (shl_ok (hs.congr k01.wr) h16₁ ((k₁.gpr .x14 (by decide)).trans h14₀) hw1 (by omega_arith)
    (by omega_arith)) fun s₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  have k02 := k01.trans k₂
  rw [m₁, m₀, c₁, hc₀] at hv₂
  rw [m₁, m₀] at ho₂
  simp only [Bool.toNat_false, Nat.add_zero] at hv₂
  -- `x16 := R`, `x14 := w + 1`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iR .x16 ((k02.gpr .x0 (by decide)).trans h0)
      ((k02.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16₃, m₃, c₃⟩, k₃⟩ => WP.mono (WP.keep [.x14]
      (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (w + 1) ∧ t.mem = s₃.mem ∧ t.c = s₃.c) (by
        brun [((k₂.trans k₃).gpr .x12 (by decide)).trans ((k01.gpr .x12 (by decide)).trans h12), ofNat_add_ofNat])
        (by decide) (by decide) (by decide +kernel))
    fun s₄ ⟨⟨h14₄, m₄, c₄⟩, k₄⟩ => ?_))
  have k04 := (k02.trans k₃).trans k₄
  -- `R := 2 R + c₁`.
  refine WP.mono (shl_ok (hs.congr k04.wr) ((k₄.gpr .x16 (by decide)).trans h16₃) h14₄ (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t ⟨hv, _, ho, k₅⟩ => ?_
  rw [m₄, m₃] at hv ho
  rw [c₄, c₃] at hv
  have hQ' : wv t.mem B (slot w iQ) w = wv s₂.mem B (slot w iQ) w :=
    ho.wv (by omega_arith) (by omega_arith)
  have hR' : wv s₂.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iR) (w + 1) :=
    ho₂.wv (by omega_arith) (by omega_arith)
  have hQlt := wv_lt s₂.mem B (slot w iQ) w
  have hQs := wv_lt s.mem B (slot w iQ) w
  have hc1 : s₂.c.toNat = wv s.mem B (slot w iQ) w / 2 ^ (64 * w - 1) := by
    rw [← two_mul_div (by omega_arith), ← hv₂, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hQlt]
    simp
  have k5 := k04.trans k₅
  have k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨?_, fun hRlt => ?_, (k15.gpr .x7 (by decide)).trans h7₀, ?_,
    k5.mono (by simp)⟩
  · rw [hQ', ← hv₂, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQlt]
  · rw [hR'] at hv
    have hc1' : s₂.c.toNat ≤ 1 := Bool.toNat_le _
    have : 2 * wv s.mem B (slot w iR) (w + 1) + s₂.c.toNat < 2 ^ (64 * (w + 1)) := by
      rw [show 64 * (w + 1) = 64 * w + 64 by omega_arith, Nat.pow_add]
      have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
      omega_arith
    have hc2 : t.c.toNat = 0 := by
      rcases Bool.toNat_le t.c |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h | h
      · exact h
      · rw [h] at hv; omega_arith
    rw [hc2] at hv
    omega_arith
  · intro x hx
    have a := hx (ar w iQ) (by simp)
    have b := hx (ar w iR) (by simp)
    rw [ho x (by dsimp only at b; omega_arith), ho₂ x (by dsimp only at a; omega_arith)]

/-- `carryMask`: `x15 := mask C`. -/
theorem carryMask_ok (s : State) (h7 : s.gpr .x7 = 0) :
    WP isa (.block carryMask) s fun t =>
      (t.gpr .x15 = mask s.c ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [.x4, .x15] s t := by
  refine WP.keep [.x4, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [carryMask, h7]
  cases s.c <;> rfl

/-- The subtraction of the divisor and the selection: `[r] := [r] - [d]` if
it does not borrow, over `w + 1` words, and `x15` the mask of no borrow. -/
theorem divSub_ok {s : State} {B : Addr} {Z w : Nat} {iR iD iT : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (seqs (divSubP iR iD iT)) s fun t =>
      t.gpr .x15 = mask (!decide (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w)) ∧
      wv t.mem B (slot w iR) (w + 1) = (if wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w then
        wv s.mem B (slot w iR) (w + 1) else wv s.mem B (slot w iR) (w + 1) - wv s.mem B (slot w iD) w) ∧
      t.gpr .x7 = 0 ∧ Frm B [ar w iR, ar w iT] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have pRD := slot_sep (w := w) dRD
  have pRT := slot_sep (w := w) dRT
  have pDT := slot_sep (w := w) dDT
  simp only [divSubP, seqs, List.append_assoc]
  -- `x7 := 0`, `x14 := w`, the carry set, the bases.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) (by brun [h12])
      (by decide) (by decide) (by decide +kernel))
    fun s₀ ⟨⟨h7₀, h14₀, hc₀, m₀⟩, k₀⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iR .x16
      ((k₀.gpr .x0 (by decide)).trans h0) ((k₀.gpr .x11 (by decide)).trans h11))
    fun s₁ ⟨⟨h16₁, m₁, c₁⟩, k₁⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iD .x17
      (((k₀.trans k₁).gpr .x0 (by decide)).trans h0) (((k₀.trans k₁).gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h17₂, m₂, c₂⟩, k₂⟩ => WP.mono (base_ok iT .x13
      (((k₀.trans k₁).trans k₂ |>.gpr .x0 (by decide)).trans h0)
      (((k₀.trans k₁).trans k₂ |>.gpr .x11 (by decide)).trans h11))
    fun s₃ ⟨⟨h13₃, m₃, c₃⟩, k₃⟩ => ?_))))
  have k03 := ((k₀.trans k₁).trans k₂).trans k₃
  have e16 : s₃.gpr .x16 = off B (slot w iR) := ((k₂.trans k₃).gpr .x16 (by decide)).trans h16₁
  have e17 : s₃.gpr .x17 = off B (slot w iD) := (k₃.gpr .x17 (by decide)).trans h17₂
  have e14 : s₃.gpr .x14 = BitVec.ofNat 64 w := (((k₁.trans k₂).trans k₃).gpr .x14 (by decide)).trans h14₀
  have ec : s₃.c = true := by rw [c₃, c₂, c₁, hc₀]
  have m03 : s₃.mem = s.mem := by rw [m₃, m₂, m₁, m₀]
  -- `T := R - D` over `w` words.
  have h0' : SubInv s₃ B Z (slot w iR) (slot w iD) (slot w iT) 0 s₃ :=
    ⟨hs.congr k03.wr, Keep.refl _ _, by rw [e16]; rfl, by rw [e17]; rfl, by rw [h13₃]; rfl,
      Outside.refl _ _ _ _, by rw [ec]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (SubInv s₃ B Z (slot w iR) (slot w iD) (slot w iT))
    (fun j hj t hI _ => subStep_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hj hI) h0' e14)
    fun s₄ hI => ?_)
  have hs₄ := hI.scr
  have k₄ := hI.keep
  have hR₄ : word s₄.mem B (slot w iR + 8 * w) = word s.mem B (slot w iR + 8 * w) := by
    rw [hI.out.word (by omega_arith) (by omega_arith), m03]
  have e7 : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans ((((k₁.trans k₂).trans k₃).gpr .x7 (by decide)).trans h7₀)
  have k04 := k03.trans k₄
  -- The top word: `T_w := R_w - b₁`, and `x15` the mask of the carry.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (slot w iT + 8 * w))
        (word s.mem B (slot w iR + 8 * w) + ~~~(0 : BitVec 64) + BitVec.ofNat 64 s₄.c.toNat) ∧
      t.c = decide (2 ^ 64 ≤ (word s.mem B (slot w iR + 8 * w)).toNat + (~~~(0 : BitVec 64)).toNat + s₄.c.toNat) ∧
      t.gpr .x7 = 0)
    (by brun [hI.x16, hI.x13, e7, hs₄.ld (show slot w iR + 8 * w + 8 ≤ Z by omega_arith),
      hs₄.st (show slot w iT + 8 * w + 8 ≤ Z by omega_arith), hR₄])
    (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨m₅, hc₅, h7₅⟩, k₅⟩ => WP.block_append_iff.mpr (WP.mono (carryMask_ok s₅ h7₅)
    fun s₆ ⟨⟨h15₆, m₆, c₆⟩, k₆⟩ => ?_)))
  have k46 := k₅.trans k₆
  have k06 := k04.trans k46
  refine WP.block_append_iff.mpr (WP.mono (base_ok iT .x16 ((k06.gpr .x0 (by decide)).trans h0)
      ((k06.gpr .x11 (by decide)).trans h11))
    fun s₇ ⟨⟨h16₇, m₇, _⟩, k₇⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iR .x17
      ((k06.trans k₇ |>.gpr .x0 (by decide)).trans h0) ((k06.trans k₇ |>.gpr .x11 (by decide)).trans h11))
    fun s₈ ⟨⟨h17₈, m₈, _⟩, k₈⟩ => WP.mono (WP.keep (c := .block [.addImm .x .x14 .x12 1]) [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (w + 1) ∧
      t.mem = s₈.mem)
      (by brun [(k06.trans k₇ |>.trans k₈ |>.gpr .x12 (by decide)).trans h12, ofNat_add_ofNat])
      (by decide) (by decide) (by decide +kernel))
    fun s₉ ⟨⟨h14₉, m₉⟩, k₉⟩ => ?_))
  have k79 := (k₇.trans k₈).trans k₉
  -- The value of `T` over `w + 1` words.
  have hval := hI.val
  have hT : wv s₉.mem B (slot w iT) (w + 1) + wv s.mem B (slot w iD) w =
      wv s.mem B (slot w iR) (w + 1) + 2 ^ (64 * (w + 1)) * (!s₅.c).toNat := by
    rw [m₉, m₈, m₇, m₆, m₅, wv_writeW_top _ _ _ _ _ (by omega_arith), wv, pow64_succ, hc₅]
    rw [m03] at hval
    have hs := sbcs_toNat (word s.mem B (slot w iR + 8 * w)) 0 s₄.c
    have h00 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h00, Nat.add_zero] at hs
    grind
  have hb : (!s₅.c) = decide (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w) :=
    lt_of_borrow (wv_lt _ _ _ _) hT
  -- The selection.
  have e15 : s₉.gpr .x15 = mask (!decide (wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w)) := by
    rw [(k79.gpr .x15 (by decide)), h15₆, ← hb, Bool.not_not]
  refine WP.mono (selLoop_ok (hI.scr.congr (k46.trans k79).wr) ((k₈.trans k₉ |>.gpr .x16 (by decide)).trans h16₇)
    ((k₉.gpr .x17 (by decide)).trans h17₈) h14₉ e15 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, ho, k₁₀⟩ => ?_
  have hR₉ : wv s₉.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iR) (w + 1) := by
    rw [m₉, m₈, m₇, m₆, m₅, (writeW_outside s₄.mem B _ (by omega_arith)).wv (by omega_arith) (by omega_arith),
      hI.out.wv (by omega_arith) (by omega_arith), m03]
  refine ⟨(k₁₀.gpr .x15 (by decide)).trans e15, ?_, ?_, ?_, (k06.trans (k79.trans k₁₀)).mono (by simp)⟩
  · rw [hv, hR₉]
    cases h5 : s₅.c
    · rw [h5] at hb
      have : wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w := by simpa using hb.symm
      simp [this]
    · rw [h5] at hb hT
      have : ¬ wv s.mem B (slot w iR) (w + 1) < wv s.mem B (slot w iD) w := by simpa using hb.symm
      simp only [this, Bool.not_false, decide_false, ite_true, ite_false]
      simp only [Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hT
      omega_arith
  · exact (k₁₀.gpr .x7 (by decide)).trans ((k79.gpr .x7 (by decide)).trans ((k₆.gpr .x7 (by decide)).trans h7₅))
  · intro x hx
    have a := hx (ar w iR) (by simp)
    have b := hx (ar w iT) (by simp)
    dsimp only at a b
    rw [ho x (by omega_arith), m₉, m₈, m₇, m₆, m₅, writeW_outside s₄.mem B _ (by omega_arith) x (by omega_arith),
      hI.out x (by omega_arith), m03]

/-- A number of `w ≥ 1` words is its low word and the `w - 1` above. -/
theorem wv_low {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  rw [show w = 1 + (w - 1) by omega_arith, wv_add, show 1 + (w - 1) - 1 = w - 1 by omega_arith]
  simp [wv]

/-- An even word or'ed with the low bit of a mask. -/
theorem or_bit {x : BitVec 64} (hx : x.toNat % 2 = 0) (c : Bool) :
    (x ||| (1#64 &&& mask c)).toNat = x.toNat + (if c then 1 else 0) := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.toNat_or, Nat.or_comm, show (1#64).toNat = 1 from rfl]
    rw [show x.toNat = 2 * (x.toNat / 2) by omega_arith, Nat.or_comm]
    have := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := 1) (by decide) (x.toNat / 2)
    simp only [Nat.pow_one] at this
    rw [← this]

/-- The quotient's new bit (`x15` the mask of no borrow `c`) into word 0 of
`[q]`, and the step counter `x6` counted down. -/
theorem divBit_ok {s : State} {B : Addr} {Z w : Nat} {iQ : Nat} {c : Bool} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h15 : s.gpr .x15 = mask c)
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hQ : iQ < 16)
    (hev : (word s.mem B (slot w iQ)).toNat % 2 = 0) :
    WP isa (.block (divBitP iQ)) s fun t =>
      t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      wv t.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w + (if c then 1 else 0) ∧
      Frm B [ar w iQ] s.mem t.mem ∧ Keep [.x3, .x4, .x6, .x16] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  rw [divBitP, WP.block_append_iff]
  refine WP.mono (base_ok iQ .x16 h0 h11) fun s₁ ⟨⟨h16, m₁, _⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have hw0 : word s₁.mem B (slot w iQ) = word s.mem B (slot w iQ) := by rw [m₁]
  refine WP.mono (WP.keep [.x3, .x4, .x6] (Q := fun t => t.gpr .x6 = s₁.gpr .x6 - BitVec.ofNat 64 1 ∧
      t.mem = s₁.mem.writeW (off B (slot w iQ)) (word s.mem B (slot w iQ) ||| (1#64 &&& mask c))) (by
      brun [h16, (k₁.gpr .x15 (by decide)).trans h15, hs₁.ld (d := slot w iQ) (by omega_arith),
        hs₁.st (d := slot w iQ) (by omega_arith), hw0]; rfl) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h6t, mt⟩, k₂⟩ => ?_
  refine ⟨by rw [h6t, k₁.gpr .x6 (by decide)], ?_, ?_, (k₁.trans k₂).mono (by simp)⟩
  · rw [mt, wv_low hw1, wv_low (m := s.mem) hw1, word_writeW_self, or_bit hev,
      (writeW_outside s₁.mem B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith), m₁]
    omega_arith
  · intro x hx
    have a := hx (ar w iQ) (by simp)
    dsimp only at a
    rw [mt, writeW_outside s₁.mem B _ (by omega_arith) x (by omega_arith), m₁]

/-- The registers `divStep` and `inverse`'s step may change. -/
def stepRegs : List Reg := [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17]

/-- One step of `divmod`: `VG.Proof.Rsa.divStep` while the remainder is below the
divisor. -/
theorem divStepCode_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR iD iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) s fun t =>
      t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧ Keep stepRegs s t ∧
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
  rw [VG.Impl.Rsa.AArch64.Keys.divStep]
  refine wp_seqs_append (by simp [divShiftP]) (by simp) (WP.mono (divShift_ok hs h0 h12 h11 hw1 hw hZ hQ hR dQR)
    fun s₁ ⟨hQ₁, hR₁, _, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [divSubP]) (by simp) (WP.mono (divSub_ok (hs.congr k₁.wr)
    ((k₁.gpr .x0 (by decide)).trans h0) ((k₁.gpr .x12 (by decide)).trans h12)
    ((k₁.gpr .x11 (by decide)).trans h11) hw1 hw hZ hR hD hT dRD dRT (by omega_arith))
    fun s₂ ⟨h15₂, hR₂, _, f₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hD₁ : wv s₁.mem B (slot w iD) w = wv s.mem B (slot w iD) w :=
    f₁.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have hQ₂ : wv s₂.mem B (slot w iQ) w = wv s₁.mem B (slot w iQ) w :=
    f₂.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have hQ2' : wv s₂.mem B (slot w iQ) w = 2 * wv s.mem B (slot w iQ) w % 2 ^ (64 * w) := hQ₂.trans hQ₁
  have hev : (word s₂.mem B (slot w iQ)).toNat % 2 = 0 := by
    have d1 : 2 ∣ 2 ^ (64 * w) := ⟨2 ^ (64 * w - 1), by rw [← Nat.pow_succ']; congr 1; omega_arith⟩
    rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), hQ2', Nat.mod_mod_of_dvd _ d1]
    omega_arith
  simp only [seqs]
  refine WP.mono (divBit_ok (hs.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h0) ((k12.gpr .x11 (by decide)).trans h11)
    h15₂ hw1 hw hZ hQ hev)
    fun t ⟨h6t, hQt, f₃, k₃⟩ => ⟨by rw [h6t, k12.gpr .x6 (by decide)], ?_, (k12.trans k₃).mono (by simp [stepRegs]),
      fun hlt => ?_⟩
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
      f₃.wv_eq (fun r hr => by simp at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
    simp only [VG.Proof.Rsa.divStep]
    rw [hQt, hQ2', hRt, hR₂, hD₁, hR₁']
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]

/-- The invariant of `divmod`'s loop after `j` steps from `s`, for the
dividend `N` and the divisor `D`. -/
structure DivInv (s : State) (B : Addr) (Z w iQ iR iD iT N D : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  x12 : t.gpr .x12 = BitVec.ofNat 64 w
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  frm : Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem
  keep : Keep (.x11 :: .x12 :: stepRegs) s t
  val : 0 < D → (wv t.mem B (slot w iR) (w + 1), wv t.mem B (slot w iQ) w) = divIter D (64 * w) j (0, N)

/-- `divmod`: the remainder of `[q]` by `[d]` into `[r]` (`w + 1` words) and
the quotient into `[q]`, if `[d]` is not zero. -/
theorem divmod_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR iD iT : Nat} (h : Ws s B Z w)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧ Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (0 < wv s.mem B (slot w iD) w →
        wv t.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iQ) w % wv s.mem B (slot w iD) w ∧
        wv t.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w / wv s.mem B (slot w iD) w) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.w1; omega_arith
  have hw := h.w2
  have sQ := Nat.le_trans (slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have pQR := slot_sep (w := w) dQR
  have pRD := slot_sep (w := w) dRD
  have pRT := slot_sep (w := w) dRT
  have pQD := slot_sep (w := w) dQD
  have pDT := slot_sep (w := w) dDT
  unfold divmod divInit
  simp only [seqs, List.cons_append, List.nil_append]
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h hR) fun s₁ ⟨hz, ho, h12₁, h11₁, _, k₁⟩ => ?_)
  have hN₁ : wv s₁.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w := ho.wv (by omega_arith) (by omega_arith)
  have hD₁ : wv s₁.mem B (slot w iD) w = wv s.mem B (slot w iD) w := ho.wv (by omega_arith) (by omega_arith)
  have hR₁ : wv s₁.mem B (slot w iR) (w + 1) = 0 := by
    have := wv_add s₁.mem B (slot w iR) (w + 1) 1
    rw [show w + 1 + 1 = w + 2 by omega_arith, hz] at this
    omega_arith
  -- `x6 := 64 w`.
  refine WP.seq (WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * w) ∧ t.mem = s₁.mem)
    (by brun [h12₁, shl_ofNat (show w * 2 ^ 6 < 2 ^ 64 by omega_arith)]; congr 1; omega_arith)
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h6₂, m₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  -- The loop.
  refine WP.mono (wp_countdown (N := 64 * w) (by omega_arith) (by omega_arith)
    (DivInv s B Z w iQ iR iD iT (wv s.mem B (slot w iQ) w) (wv s.mem B (slot w iD) w))
    (fun j hj t hI _ => ?_)
    ⟨hs.congr k12.wr, (k12.gpr .x0 (by decide)).trans h.x0, (k₂.gpr .x12 (by decide)).trans h12₁,
      (k₂.gpr .x11 (by decide)).trans h11₁,
      Frm.of_outside (by rw [m₂]; exact ho.mono (Nat.le_refl _) (Nat.le_refl _)) (by simp),
      k12.mono (by simp [stepRegs]), fun _ => by rw [m₂, hR₁, hN₁]; rfl⟩ h6₂)
    fun t hI => ⟨hI.x0, hI.frm, hI.keep, fun hD0 => ?_⟩
  · have hDt : wv t.mem B (slot w iD) w = wv s.mem B (slot w iD) w :=
      hI.frm.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    refine WP.mono (divStepCode_ok hI.scr hI.x0 hI.x12 hI.x11 hw1 hw hZ hQ hR hD hT dQR dQD dQT dRD dRT dDT)
      fun t' ⟨h6', f', k', hv'⟩ => ⟨?_, h6'⟩
    refine ⟨hI.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hI.x0, (k'.gpr .x12 (by decide)).trans hI.x12,
      (k'.gpr .x11 (by decide)).trans hI.x11, hI.frm.trans f', (hI.keep.trans k').mono (by simp [stepRegs]),
      fun hD0 => ?_⟩
    obtain ⟨q, hlt, -, -, -⟩ := divIter_inv hD0 (wv_lt s.mem B (slot w iQ) w) j (by omega_arith)
    have hv := hI.val hD0
    have hRt : wv t.mem B (slot w iR) (w + 1) < wv t.mem B (slot w iD) w := by
      rw [hDt, show wv t.mem B (slot w iR) (w + 1) = _ from congrArg Prod.fst hv]; exact hlt
    rw [hv' hRt, hDt, hv]
    rfl
  · have := hI.val hD0
    rw [divIter_done hD0 (wv_lt s.mem B (slot w iQ) w), Prod.ext_iff] at this
    exact this

end VG.Proof.Rsa.AArch64
