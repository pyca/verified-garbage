import VerifiedGarbage.Proof.Mont.Arm.Row

/-!
# Montgomery arithmetic on 32-bit ARM: the loop of the multiplication

A digit's row (`digitRow`), at `r0 = r12 + 4i`, adds `u [b]` and then `q m`
to the window of `D + 2` digits at `acc + 4i`, which holds `T < 2m` (the
digit above it being zero): `q = t₀ m' mod 2¹⁶` makes the sum's low digit
zero, so the window one digit up holds `(T + u B + q m) / 2¹⁶`, below `2m`
again (`digitRow_ok`). An iteration of the loop (`row`) does the rows of
the two digits of a word of `[a]` (`row_ok`); `Z` is whether it was the last.
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr)

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- The registers the multiplication's rows write: `clob` but `r4`, which
the rows leave for a pointer. -/
def rowClob : List Reg := [.r0, .r1, .r2, .r3, .r5, .r6, .r7, .r8, .r9]

/-- A register outside `rowClob` is outside any list of its registers. -/
theorem not_mem_of_rowClob {r : Reg} (h : r ∉ rowClob) {l : List Reg} (hl : ∀ x ∈ l, x ∈ rowClob := by decide) :
    r ∉ l := fun hr => h (hl r hr)

/-- A register outside `clob` is outside `rowClob`. -/
theorem not_mem_rowClob {r : Reg} (h : r ∉ clob) : r ∉ rowClob :=
  fun hr => h ((by decide : ∀ x ∈ rowClob, x ∈ clob) r hr)

/-- A register outside `clob` is outside any list of its registers. -/
theorem not_mem_of_clob {r : Reg} (h : r ∉ clob) {l : List Reg} (hl : ∀ x ∈ l, x ∈ clob := by decide) :
    r ∉ l := fun hr => h (hl r hr)

/-- `t₀ + (t₀ m' mod 2¹⁶) m ≡ 0 (mod 2¹⁶)` when `m m' ≡ -1`. -/
theorem mont_low16 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 16 = 0) :
    (t0 + t0 * minv % 2 ^ 16 * m) % 2 ^ 16 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 16), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega_arith,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2¹⁶`. -/
theorem minv16_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0 := by
  rw [minv16, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 16 ∣ 2 ^ 64 from ⟨2 ^ 48, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 16) (hB : B < m) (hq : q < 2 ^ 16) :
    T + u * B + q * m < 2 ^ 16 * (2 * m) := by
  have h1 : u * B ≤ (2 ^ 16 - 1) * B := Nat.mul_le_mul_right _ (by omega_arith)
  have h2 : q * m ≤ (2 ^ 16 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
  omega_arith

/-- The low digit of a window of digits. -/
theorem dval_low {m : Mem} {base : Addr} {d k : Nat} (h : Digs m base d (k + 1)) :
    dval m base d (k + 1) % 2 ^ 16 = w32 m base d := by
  rw [show k + 1 = 1 + k by omega_arith, dval_append, show dval m base d 1 = w32 m base d by
    simp [dval], Nat.mul_comm, show 16 * 1 = 16 by rfl, Nat.add_mul_mod_self_right]
  have := h 0 (by omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero] at this
  exact Nat.mod_eq_of_lt this

/-- The window one digit up, when the low digit is zero and the digit above
the window is zero. -/
theorem dval_shift {m : Mem} {base : Addr} {d k : Nat} (h0 : w32 m base d = 0) (htop : w32 m base (d + 4 * (k + 1)) = 0) :
    2 ^ 16 * dval m base (d + 4) (k + 1) = dval m base d (k + 1) := by
  rw [show k + 1 = 1 + k by omega_arith, dval_append m base d 1 k, show dval m base d 1 = w32 m base d by simp [dval], h0,
    Nat.zero_add, show 1 + k = k + 1 by omega_arith, dval, show d + 4 + 4 * k = d + 4 * (k + 1) by omega_arith, htop,
    show 16 * 1 = 16 by rfl]
  simp

/-- A pointer moved up 4 bytes. -/
theorem ptr_add4 (e : BitVec 32) (x : Nat) :
    e + BitVec.ofNat 32 x + 4 = e + BitVec.ofNat 32 (x + 4) := by
  rw [BitVec.add_assoc]
  refine congrArg (e + ·) ?_
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_arith

/-- A pointer moved up a word. -/
theorem ptr_succ (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  refine congrArg (e + ·) ?_
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_arith

/-- What a digit's row needs of the layout: `[b]` and the modulus (`W`
words, `D = 2W` digits) apart from the window and the digit above it. -/
structure RowLay (W size w b mo : Nat) : Prop where
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  w_le : w + 4 * (2 * W + 3) ≤ size
  sb : b + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ b
  smo : mo + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ mo

/-- A digit's row: from the window `T < 2m` at `w = acc + 4i` (the digit
above it zero), the window one digit up holds `(T + u B + q m) / 2¹⁶`
(`[b]` read at `[rb + d]`, `rb = r12 + K`). -/
theorem digitRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W D acc b h i w m : Nat}
    {rb : Reg} {K d : Nat} (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = b) (hrb : rb ∉ rowClob)
    (_hW : words M = W) (hD : digits M = D) (hDW : D = 2 * W) (hL : RowLay W size w b M.mo)
    (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) (hd : Digs s.mem base w (D + 2))
    (hT : dval s.mem base w (D + 2) < 2 * m) (htop : w32 s.mem base (w + 4 * (D + 2)) = 0) :
    WP isa (.block (digitRow M acc rb d h)) s fun u =>
      u.gpr .r0 = u.gpr .r12 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      Outside base w (4 * (D + 2)) s.mem u.mem ∧ Digs u.mem base (w + 4) (D + 2) ∧
      (∃ q, q < 2 ^ 16 ∧ 2 ^ 16 * dval u.mem base (w + 4) (D + 2) =
        dval s.mem base w (D + 2) + hdig (s.gpr .r8).toNat h * val32 s.mem base b W + q * m) ∧
      Rest [.r0, .r2, .r3, .r5, .r7] s u := by
  have hn := hs.nowrap
  obtain ⟨hb_le, hmo_le, hw_le, hsb, hsmo⟩ := hL
  subst hDW
  have hm0 : m < 2 ^ (16 * (2 * W)) := by
    rw [← hm, show 16 * (2 * W) = 32 * W by omega_arith]; exact val32_lt _ _ _ _
  simp only [digitRow, hD, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_half hh h6 fun s₁ u₁ => ?_
  have K₁ : Rest [.r2, .r3, .r5, .r7] s s₁ := u₁.rest (by simp)
  have hs₁ := hs.of_rest K₁ (by decide)
  have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
  have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  have hU := hdig_lt (s.gpr .r8).toNat h
  have hu₁ : (s₁.gpr .r2).toNat = hdig (s.gpr .r8).toNat h := by
    rw [u₁.gpr, BitVec.toNat_ofNat]; omega_arith
  rw [← u₁.mem] at hm hB hd hT htop
  have hBp : pval s₁.mem base b (2 * W) = val32 s₁.mem base b W := pval_words _ _ _ _
  have hlt₁ : dval s₁.mem base w (2 * W + 2) + (s₁.gpr .r2).toNat * pval s₁.mem base b (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hBp, hu₁, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_arith, Nat.pow_add]
    have : hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W ≤ (2 ^ 16 - 1) * m :=
      Nat.mul_le_mul (by omega_arith) (by omega_arith)
    have : (2 ^ 16 - 1) * m + 2 * m < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : (2 ^ 16 + 1) * m < (2 ^ 16 + 1) * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_arith)
      omega_arith
    omega_arith
  have hrb' : rb ∉ [.r3, .r5, .r7] := not_mem_of_rowClob hrb
  have hb₁ : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₁.gpr _ (not_mem_of_rowClob hrb), K₁.gpr _ (by decide)]; exact hb
  refine VG.Proof.X25519.Arm.WP.append (mulRow_ok hs₁ hb₁ hK hrb' h6₁ hp₁ hw hb_le (D := 2 * W) (Nat.le_refl _) (by omega_arith)
    (by omega_arith) (by rw [hu₁]; exact hU) hd hlt₁) fun s₂ ⟨O₂, V₂, D₂, K₂⟩ => ?_
  have K₁₂ := K₁.trans (K₂.mono (by simp))
  have hs₂ := hs.of_rest K₁₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₂.gpr _ (by decide)]; exact h6
  have hp₂ : s₂.gpr .r0 = s₂.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₁₂.gpr _ (by decide), K₁₂.gpr _ (by decide)]; exact hp
  rw [hBp, hu₁] at V₂
  -- q
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs₂.ea_at hp₂ (d := acc) (by omega_arith)) (hs₂.read (by omega_arith))
    fun s₃ u₃ => ?_
  refine wp_movw fun s₄ u₄ => ?_
  refine wp_mul fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have K₆ : Rest [.r2, .r3, .r5, .r7] s₂ s₆ :=
    ((u₃.rest (by simp)).trans (u₄.rest (by simp))).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  have K₁₆ := K₁₂.trans K₆
  have hs₆ := hs.of_rest K₁₆ (by decide)
  have h6₆ : s₆.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₆.gpr _ (by decide)]; exact h6
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp₂
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have ht0 : w32 s₂.mem base w = (dval s₁.mem base w (2 * W + 2) + hdig (s.gpr .r8).toNat h *
      val32 s₁.mem base b W) % 2 ^ 16 := by
    rw [← V₂, dval_low D₂]
  have hq : (s₆.gpr .r2).toNat = w32 s₂.mem base w * (minv16 M).toNat % 2 ^ 16 := by
    have h6₅ : s₅.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact h6₂
    have hmv : (minv16 M).toNat % 2 ^ 32 = (minv16 M).toNat :=
      Nat.mod_eq_of_lt (Nat.lt_trans (minv16 M).isLt (by decide))
    rw [u₆.gpr, dpVal, toNat_and_r6 h6₅, u₅.gpr, BitVec.toNat_mul, u₄.gpr, u₄.other _ (by decide), u₃.gpr,
      BitVec.toNat_setWidth, hmv, Nat.mod_mod_of_dvd _ (show 2 ^ 16 ∣ 2 ^ 32 from ⟨2 ^ 16, by decide⟩), ← hw]
  have hq16 : (s₆.gpr .r2).toNat < 2 ^ 16 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  rw [← m₆] at D₂ V₂ O₂
  have hmo₆ : val32 s₆.mem base M.mo W = m := by
    rw [O₂.val32 (by omega_arith) (by omega_arith)]; exact hm
  have hMp : pval s₆.mem base M.mo (2 * W) = m := by rw [pval_words, hmo₆]
  have hlt₂ : dval s₆.mem base w (2 * W + 2) + (s₆.gpr .r2).toNat * pval s₆.mem base M.mo (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hMp, V₂, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_arith, Nat.pow_add]
    have hb1 : val32 s₁.mem base b W < m := hB
    have := row_lt hT hU hb1 hq16
    have : 2 ^ 16 * (2 * m) < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : 2 * 2 ^ 16 * m < 2 * 2 ^ 16 * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_arith)
      omega_arith
    omega_arith
  refine VG.Proof.X25519.Arm.WP.append (mulRow_ok hs₆ (rb := .r12) (K := 0) (by simp) (Nat.zero_add _) (by decide)
    h6₆ hp₆ hw hmo_le (D := 2 * W) (Nat.le_refl _) (by omega_arith)
    (by omega_arith) hq16 D₂ hlt₂) fun s₇ ⟨O₇, V₇, D₇, K₇⟩ => ?_
  have K₁₇ := K₁₆.trans (K₇.mono (by simp))
  refine wp_dp (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  rw [hMp, V₂] at V₇
  have m₈ : s₈.mem = s₇.mem := u₈.mem
  -- The window's low digit is zero, and the one above it too.
  generalize hT1 : dval s₁.mem base w (2 * W + 2) + hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W = T1 at *
  generalize hqv : (s₆.gpr .r2).toNat = q at *
  have hz : w32 s₇.mem base w = 0 := by
    rw [← dval_low D₇, V₇, show (T1 + q * m) % 2 ^ 16 = (T1 % 2 ^ 16 + q * m) % 2 ^ 16 by omega_arith, hq, ← ht0]
    exact mont_low16 _ _ _ hinv
  have htop' : w32 s₇.mem base (w + 4 * (2 * W + 2)) = 0 := by
    rw [O₇.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith)]; exact htop
  have hsh := dval_shift hz htop'
  refine ⟨?_, ?_, ?_, ⟨q, hq16, ?_⟩, ?_⟩
  · rw [u₈.gpr, dpVal, u₈.other _ (by decide), K₇.gpr _ (by decide), K₇.gpr _ (by decide), hp₆]
    exact ptr_succ _ _
  · rw [m₈, ← u₁.mem]
    exact (O₂.mono (Nat.le_refl _) (by omega_arith)).trans (O₇.mono (Nat.le_refl _) (by omega_arith))
  · intro j hj
    rw [m₈]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show w + 4 + 4 * j = w + 4 * (j + 1) by omega_arith]; exact D₇ (j + 1) (by omega_arith)
    · rw [show w + 4 + 4 * (2 * W + 1) = w + 4 * (2 * W + 2) by omega_arith, htop']; decide
  · rw [m₈, hsh, V₇, ← hT1, ← u₁.mem]
  · exact ((((K₁.trans (K₂.mono (by simp))).trans K₆).trans (K₇.mono (by simp))).mono
      (ws' := [.r0, .r2, .r3, .r5, .r7]) (by simp)).trans (u₈.rest (by simp))

/-! ## The loop -/

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`W`
words) in the working space and apart from the accumulator (`2D + 2 = 4W + 2`
digits at `acc`). -/
structure MulLay (W size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (4 * W + 2) ≤ size
  a_le : a + 4 * W ≤ size
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  sa : a + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ a
  sb : b + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ b
  smo : mo + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ mo

/-- The invariant of the loop, before the iteration for word `k` of `[a]`:
the window of `D + 2` digits at `acc + 8k` holds `T < 2m` with
`2^(32 k) T ≡ A B`, for the low `2k` digits `A` of `[a]`; the digits above
it are zero; `r0` points to the window and `r1` to word `k`, from `ka` bytes
into the working space, and `r9` counts the words left. -/
structure LoopInv (base : Addr) (W acc ka a b m k : Nat) (s t : State) : Prop where
  r0 : t.gpr .r0 = t.gpr .r12 + BitVec.ofNat 32 (4 * (2 * k))
  r1 : t.gpr .r1 = t.gpr .r12 + BitVec.ofNat 32 (ka + 4 * k)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (W - k)
  r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16
  out : Outside base acc (4 * (4 * W + 2)) s.mem t.mem
  rest : Rest rowClob s t
  digs : Digs t.mem base (acc + 4 * (2 * k)) (2 * W + 2)
  zeros : ∀ l, 2 * k + 2 * W + 2 ≤ l → l < 4 * W + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) =
    pval s.mem base a (2 * k) * val32 s.mem base b W + U * m

/-- The count of the loop, one less. -/
theorem cnt_dec {W k : Nat} (hk : k < W) (hW : W < 2 ^ 32) :
    BitVec.ofNat 32 (W - k) - 1 = BitVec.ofNat 32 (W - (k + 1)) := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, BitVec.toNat_ofNat]; omega_arith), h1, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega_arith

/-- The congruence of the loop, two digits on. -/
theorem cong_step {P T T' T'' A B m U u0 u1 q0 q1 : Nat} (h0 : P * T = A * B + U * m)
    (h1 : 2 ^ 16 * T' = T + u0 * B + q0 * m) (h2 : 2 ^ 16 * T'' = T' + u1 * B + q1 * m) :
    P * 2 ^ 32 * T'' = (A + u0 * P + u1 * (P * 2 ^ 16)) * B + (U + q0 * P + q1 * (P * 2 ^ 16)) * m := by
  have e1 : P * 2 ^ 32 * T'' = P * (2 ^ 16 * T') + P * 2 ^ 16 * (u1 * B + q1 * m) := by
    rw [show P * 2 ^ 32 * T'' = P * 2 ^ 16 * (2 ^ 16 * T'') by grind, h2]; grind
  have e2 : P * (2 ^ 16 * T') = A * B + U * m + P * u0 * B + P * q0 * m := by
    rw [h1, Nat.mul_add, Nat.mul_add, h0]; grind
  rw [e1, e2]; grind

/-- An iteration of the loop: the rows of the two digits of word `k` (of
`[a]`, read at `[r1 + da]`, and `[b]`, at `[rb + db]`, `rb = r12 + kb`). -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W acc a b m k : Nat}
    {ka da : Nat} (hka : ka + da = a) {rb : Reg} {kb db : Nat}
    (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b) (hrb : rb ∉ rowClob)
    (hW : words M = W) (hD : digits M = 2 * W) (hL : MulLay W size acc a b M.mo) (hk : k < W)
    (hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (I : LoopInv base W acc ka a b m k s t) :
    WP isa (.block (row M acc da rb db)) t fun u =>
      LoopInv base W acc ka a b m (k + 1) s u ∧ u.z = decide (k + 1 = W) := by
  have hn := hs.nowrap
  obtain ⟨acc_le, a_le, b_le, mo_le, sa, sb, smo⟩ := hL
  have ht := hs.of_rest I.rest (by decide)
  have hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega_arith) (by omega_arith), hm]
  have hbt : val32 t.mem base b W = val32 s.mem base b W := I.out.val32 (by omega_arith) (by omega_arith)
  have hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega_arith) (by omega_arith)
  simp only [row, List.cons_append, List.nil_append, List.append_assoc]
  have ea : State.addr (t.gpr .r1 + BitVec.ofNat 32 da) = off base (4 * k + a) := by
    rw [show 4 * k + a = ka + 4 * k + da by omega_arith]; exact ht.ea_off I.r1 (by omega_arith)
  refine wp_ldr (hs.off_lt (d := da) (by omega_arith)) ea (ht.read (by omega_arith)) fun t₁ u₁ => ?_
  have K₁ : Rest rowClob t t₁ := u₁.rest (by simp [rowClob])
  have hbR : ∀ t', Rest rowClob s t' → t'.gpr rb = t'.gpr .r12 + BitVec.ofNat 32 kb := fun t' K => by
    rw [K.gpr _ hrb, K.gpr _ (by decide)]; exact hb
  have ht₁ := ht.of_rest K₁ (by decide)
  have r8₁ : (t₁.gpr .r8).toNat = w32 s.mem base (a + 4 * k) := by
    rw [u₁.gpr, ← hat, show 4 * k + a = a + 4 * k by omega_arith]
  have m₁ : t₁.mem = t.mem := u₁.mem
  have L₀ : RowLay W size (acc + 4 * (2 * k)) b M.mo := ⟨b_le, mo_le, by omega_arith, by omega_arith, by omega_arith⟩
  refine VG.Proof.X25519.Arm.WP.append (digitRow_ok ht₁ (hbR _ (I.rest.trans K₁)) hkb hrb hW hD rfl L₀ (h := 0)
    (i := 2 * k) (by decide)
    (by rw [u₁.other _ (by decide)]; exact I.r6) (by rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact I.r0)
    (by omega_arith) (by rw [m₁, hmt]) hinv (by rw [m₁, hbt]; exact hB) (by rw [m₁]; exact I.digs) (by rw [m₁]; exact I.lt)
    (by rw [m₁, show acc + 4 * (2 * k) + 4 * (2 * W + 2) = acc + 4 * (2 * k + 2 * W + 2) by omega_arith];
        exact I.zeros _ (Nat.le_refl _) (by omega_arith))) fun t₂ ⟨p₂, O₂, D₂, ⟨q₀, hq₀, V₂⟩, K₂⟩ => ?_
  have K₁₂ : Rest rowClob t t₂ := K₁.trans (K₂.mono (by simp [rowClob]))
  have ht₂ := ht.of_rest K₁₂ (by decide)
  rw [m₁] at O₂ V₂
  have hmt₂ : val32 t₂.mem base M.mo W = m := by rw [O₂.val32 (by omega_arith) (by omega_arith), hmt]
  have hbt₂ : val32 t₂.mem base b W = val32 s.mem base b W := by rw [O₂.val32 (by omega_arith) (by omega_arith), hbt]
  rw [r8₁, hbt] at V₂
  have hU0 := hdig_lt (w32 s.mem base (a + 4 * k)) 0
  have hT' : dval t₂.mem base (acc + 4 * (2 * k) + 4) (2 * W + 2) < 2 * m := by
    have := row_lt I.lt hU0 hB hq₀
    omega_arith
  have L₁ : RowLay W size (acc + 4 * (2 * k) + 4) b M.mo := ⟨b_le, mo_le, by omega_arith, by omega_arith, by omega_arith⟩
  have r8₂ : t₂.gpr .r8 = t₁.gpr .r8 := K₂.gpr _ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (digitRow_ok ht₂ (hbR _ (I.rest.trans K₁₂)) hkb hrb hW hD rfl L₁ (h := 1)
    (i := 2 * k + 1) (by decide)
    (by rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r6) p₂ (by omega_arith) hmt₂ hinv
    (by rw [hbt₂]; exact hB) D₂ hT'
    (by rw [O₂.w32 (by omega_arith) (by omega_arith), show acc + 4 * (2 * k) + 4 + 4 * (2 * W + 2) =
        acc + 4 * (2 * k + 2 * W + 3) by omega_arith]; exact I.zeros _ (by omega_arith) (by omega_arith)))
    fun t₃ ⟨p₃, O₃, D₃, ⟨q₁, hq₁, V₃⟩, K₃⟩ => ?_
  rw [r8₂, r8₁, hbt₂] at V₃
  refine wp_dp (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  have r9₄ : t₄.gpr .r9 = BitVec.ofNat 32 (W - k) := by
    rw [u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r9
  have hU1 := hdig_lt (w32 s.mem base (a + 4 * k)) 1
  have hT'' : dval t₃.mem base (acc + 4 * (2 * k) + 4 + 4) (2 * W + 2) < 2 * m := by
    have := row_lt hT' hU1 hB hq₁
    omega_arith
  have e8 : acc + 4 * (2 * (k + 1)) = acc + 4 * (2 * k) + 4 + 4 := by omega_arith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), p₃]
    congr 2
  · rw [u₅.other _ (by decide), u₄.gpr, dpVal, u₅.other _ (by decide), u₄.other _ (by decide),
      K₃.gpr _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide), I.r1, ptr_add4]
    congr 2
  · rw [u₅.gpr, r9₄]; exact cnt_dec hk (by omega_arith)
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide),
      u₁.other _ (by decide)]; exact I.r6
  · rw [m₅]
    exact I.out.trans ((O₂.mono (by omega_arith) (by omega_arith)).trans (O₃.mono (by omega_arith) (by omega_arith)))
  · exact (I.rest.trans K₁₂).trans ((K₃.mono (by simp [rowClob])).trans
      ((u₄.rest (by simp [rowClob])).trans (u₅.rest (by simp [rowClob]))))
  · rw [m₅, e8]; exact D₃
  · intro l hl1 hl2
    rw [m₅, O₃.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith)]
    exact I.zeros l (by omega_arith) hl2
  · rw [m₅, e8]; exact hT''
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + q₀ * 2 ^ (32 * k) + q₁ * (2 ^ (32 * k) * 2 ^ 16), ?_⟩
    have hc := cong_step hU V₂ V₃
    rw [m₅, e8, show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega_arith, pval, pval, hc]
    simp only [pdig, show (2 * k + 1) / 2 = k by omega_arith, show (2 * k) / 2 = k by omega_arith,
      show (2 * k + 1) % 2 = 1 by omega_arith, show (2 * k) % 2 = 0 by omega_arith,
      show 16 * (2 * k + 1) = 32 * k + 16 by omega_arith, show 16 * (2 * k) = 32 * k by omega_arith, Nat.pow_add]
  · rw [z₅, r9₄, cnt_dec hk (by omega_arith), VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith

/-- The loop of `mul`: from the invariant at word 0 to the invariant at `W`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W acc a b m : Nat}
    {ka da : Nat} (hka : ka + da = a) {rb : Reg} {kb db : Nat}
    (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b) (hrb : rb ∉ rowClob)
    (hW : words M = W) (hD : digits M = 2 * W) (hL : MulLay W size acc a b M.mo) (hW0 : 0 < W) (hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (h0 : LoopInv base W acc ka a b m 0 s t) :
    WP isa (.loop (.block (row M acc da rb db)) .ne) t fun u => LoopInv base W acc ka a b m W s u := by
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = W - k ∧ k < W ∧ LoopInv base W acc ka a b m k s t') ?_ W t ⟨0, rfl, hW0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (row_ok hs hka hb hkb hrb hW hD hL hk hW32 hm hinv hB I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = W
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, W - (k + 1), by omega_arith,
      k + 1, rfl, by omega_arith, I'⟩

end VG.Proof.Mont.Arm
