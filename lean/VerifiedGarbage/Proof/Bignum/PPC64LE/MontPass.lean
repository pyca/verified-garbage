module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontMac
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: the two passes of a round

`montMulPass_ok`: `T := T + aᵢ b`, from the `w + 1` words of `T` to `w + 2`.
`montRedPass_ok`: `T := (T + u m) / 2⁶⁴` for `u = t₀ (-m⁻¹) mod 2⁶⁴`, from `w + 2`
words to `w + 1`, if the sum fits in `w + 2` words.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-- The registers a pass writes. -/
def montPassRegs : List Reg := [.r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- The registers `montRedPass` writes. -/
def montRedRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

theorem mont_toNat_ofNat_sum {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 (a + c)).toNat + 2 ^ 64 * (BitVec.ofNat 64 (0 + (decide (2 ^ 64 ≤ a + c)).toNat)).toNat =
      a + c := by
  simp only [BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a + c <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega

theorem mont_toNat_ofNat_top {a b c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) (h : a + c + 2 ^ 64 * b < 2 ^ 128) :
    (BitVec.ofNat 64 (a + c)).toNat + 2 ^ 64 * (BitVec.ofNat 64 (b + (decide (2 ^ 64 ≤ a + c)).toNat)).toNat =
      a + c + 2 ^ 64 * b := by
  simp only [BitVec.toNat_ofNat]
  by_cases h' : 2 ^ 64 ≤ a + c <;> simp only [h', decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega

/-- Two words stored at `d`, `d + 8`, above `j` words at `d₀`. -/
theorem mont_wordsVal_write2 (m : Mem) (B : Addr) (d j : Nat) (v v' : BitVec 64) (h : d + 8 * j + 16 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (d + 8 * j + 8)) v') B d (j + 2) =
      wordsVal m B d j + 2 ^ (64 * j) * (v.toNat + 2 ^ 64 * v'.toNat) := by
  rw [show d + 8 * j + 8 = d + 8 * (j + 1) by omega_arith, mont_wordsVal_write_top _ _ _ _ _ (by omega_arith),
    mont_wordsVal_write_top _ _ _ _ _ (by omega_arith), Nat.mul_succ, Nat.pow_add]
  grind

/-! ## `T := T + aᵢ b` -/

theorem montMulHead_ok {s : State} {B : Addr} {Z da dA dB w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 w) (ha : da + 8 ≤ Z) :
    WP isa (.block montMulHead) s fun s' =>
      (s'.gpr .r17 = word s.mem B da ∧ s'.gpr .r6 = off B (da + 8) ∧ s'.gpr .r14 = off B dA ∧
        s'.gpr .r15 = off B dB ∧ s'.gpr .r16 = BitVec.ofNat 64 w ∧ s'.gpr .r18 = 0#64 ∧ s'.mem = s.mem) ∧
      Keep montPassRegs s s' := by
  refine WP.keep montPassRegs ?_ (by decide)
  unfold montMulHead
  mcrun [h6, h8, h7, h3, hs.ld ha, BitVec.add_zero]

theorem montMulTop_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (hT : dT + 16 ≤ Z) :
    WP isa (.block montMulTop) s fun s' =>
      s'.mem = (s.mem.writeW (off B dT) (BitVec.ofNat 64 ((word s.mem B dT).toNat + (s.gpr .r18).toNat))).writeW
        (off B (dT + 8)) (BitVec.ofNat 64 (0 + (decide (2 ^ 64 ≤
          (word s.mem B dT).toNat + (s.gpr .r18).toNat)).toNat)) ∧ Keep [.r22] s s' := by
  refine WP.keep [.r22] ?_ (by decide)
  unfold montMulTop
  mcrun [h14, hs.ld (show dT + 8 ≤ Z by omega_arith), hs.st (show dT + 8 ≤ Z by omega_arith),
    hs.st (show dT + 8 + 8 ≤ Z by omega_arith)]
  rfl

/-- `T := T + aᵢ b` (`montMulPass`), for `aᵢ` at `da` (pointed to by `r6`, which
is advanced), `T` (`w + 1` words, then `w + 2`) at `dA` and `b` (`w` words)
at `dB`. -/
theorem montMulPass_ok {s : State} {B : Addr} {Z da dA dB w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * w ≤ dB) :
    WP isa montMulPass s fun s' =>
      (s'.gpr .r6 = off B (da + 8) ∧ Outside B dA (8 * (w + 2)) s.mem s'.mem ∧
        wordsVal s'.mem B dA (w + 2) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w) ∧
      Keep montPassRegs s s' := by
  have hnw := hs.nowrap
  unfold montMulPass
  refine WP.seq (WP.mono (montMulHead_ok hs h6 h8 h7 h3 ha) fun s₁ ⟨⟨i17, i6, i14, i15, i16, i18, im⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (montMacLoop_ok (k := 0) (N := w) (hs.congr k₁.wr) (.inl rfl) i14 i15 i16 hw (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨j14, jout, jeq, k₂⟩ => ?_)
  refine WP.mono (montMulTop_ok (hs.congr (k₁.trans k₂).wr) j14 (by omega_arith)) fun s₃ ⟨jm, k₃⟩ => ?_
  have k23 := k₂.trans k₃
  -- The top word read is the one on entry.
  have wt : word s₂.mem B (dA + 8 * w) = word s.mem B (dA + 8 * w) := by
    rw [jout.word (by omega_arith) (by omega_arith), im]
  rw [i17, i18, im, Nat.add_zero] at jeq
  simp only [Nat.add_zero, BitVec.toNat_zero, Nat.add_zero] at jeq
  refine ⟨⟨by rw [k23.gpr _ (by decide), i6], ?_, ?_⟩, (k₁.trans k23).mono (by decide)⟩
  · rw [jm, ← im]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      (((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))
  · rw [jm, mont_wordsVal_write2 _ _ _ _ _ _ (by omega_arith), wt,
      mont_toNat_ofNat_sum (word s.mem B (dA + 8 * w)).isLt (s₂.gpr .r18).isLt, wordsVal_succ_top s.mem B dA w]
    grind

/-! ## `T := (T + u m) / 2⁶⁴` -/

/-- The arithmetic of word 0: `u m₀ + t₀`, a multiple of `2⁶⁴`, is `2⁶⁴`
times the high word of `u m₀` plus the carry of its low word plus `t₀`. -/
theorem mont_red_arith (t u m : BitVec 64) (h : ((u * m).toNat + t.toNat) % 2 ^ 64 = 0) :
    2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 (u.toNat * m.toNat / 2 ^ 64)).toNat +
      (decide (2 ^ 64 ≤ (u * m).toNat + t.toNat)).toNat)).toNat = u.toNat * m.toNat + t.toNat := by
  have hu := u.isLt
  have hm := m.isLt
  have ht := t.isLt
  have hP : u.toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul] at h ⊢
  by_cases h1 : 2 ^ 64 ≤ u.toNat * m.toNat % 2 ^ 64 + t.toNat <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem montRedHead_ok {s : State} {B : Addr} {Z dA dM w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h10 : s.gpr .r10 = off B dM) (h3 : s.gpr .r3 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 64) (hA : dA + 8 ≤ Z) (hM : dM + 8 ≤ Z)
    (hinv : ((word s.mem B dM).toNat * (s.gpr .r0).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block montRedHead) s fun s' =>
      ((s'.gpr .r17).toNat = (word s.mem B dA).toNat * (s.gpr .r0).toNat % 2 ^ 64 ∧
        2 ^ 64 * (s'.gpr .r18).toNat = (s'.gpr .r17).toNat * (word s.mem B dM).toNat + (word s.mem B dA).toNat ∧
        s'.gpr .r14 = off B dA ∧ s'.gpr .r15 = off B dM ∧ s'.gpr .r16 = BitVec.ofNat 64 (w - 1) ∧
        s'.mem = s.mem) ∧ Keep montRedRegs s s' := by
  refine WP.keep montRedRegs ?_ (by decide)
  unfold montRedHead
  mcrun [h8, h10, h3, hs.ld hA, hs.ld hM, BitVec.add_zero, ofNat_sub_one hw hw']
  refine ⟨BitVec.toNat_mul _ _, mont_red_arith _ _ _ ?_⟩
  rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mod_add_mod, Nat.add_comm]
  exact mont_low _ _ _ hinv

theorem montRedTop_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (hT : dT + 24 ≤ Z) :
    WP isa (.block montRedTop) s fun s' =>
      s'.mem = (s.mem.writeW (off B dT)
          (BitVec.ofNat 64 ((word s.mem B (dT + 8)).toNat + (s.gpr .r18).toNat))).writeW
        (off B (dT + 8)) (BitVec.ofNat 64 ((word s.mem B (dT + 16)).toNat + (decide (2 ^ 64 ≤
          (word s.mem B (dT + 8)).toNat + (s.gpr .r18).toNat)).toNat)) ∧ Keep [.r22] s s' := by
  have hnw := hs.nowrap
  have hX : ∀ v, (s.mem.writeW (off B dT) v).readW (off B (dT + 16)) 64 = word s.mem B (dT + 16) := fun v =>
    (writeW_outside s.mem B v (by omega_arith)).word (by omega_arith) (by omega_arith)
  refine WP.keep [.r22] ?_ (by decide)
  unfold montRedTop
  mcrun [h14, hs.ld (show dT + 8 + 8 ≤ Z by omega_arith), hs.st (show dT + 8 ≤ Z by omega_arith),
    hs.ld (show dT + 16 + 8 ≤ Z by omega_arith), hs.st (show dT + 8 + 8 ≤ Z by omega_arith), hX]

/-- The sum of `montRedPass`: `t₀ + 2⁶⁴ A'` (the low `w` words of `T`), `Q (X + 2⁶⁴
Y)` (its top two) and `u (m₀ + 2⁶⁴ M')`, from `2⁶⁴ c₀ = u m₀ + t₀` and the
loop's `L + P c = A' + u M' + c₀`, with `2⁶⁴ P = Q`. -/
theorem mont_red_sum {T0 A' X Y u m0 M' L P c c₀ Q : Nat} (hQ : 2 ^ 64 * P = Q) (h0 : 2 ^ 64 * c₀ = u * m0 + T0)
    (hL : L + P * c = A' + u * M' + c₀) :
    T0 + 2 ^ 64 * A' + Q * (X + 2 ^ 64 * Y) + u * (m0 + 2 ^ 64 * M') = 2 ^ 64 * L + Q * (X + c + 2 ^ 64 * Y) := by
  subst hQ
  grind

/-- `T := (T + u m) / 2⁶⁴` (`montRedPass`), for `T` (`w + 2` words, then `w + 1`)
at `dA`, `m` (`w` words) at `dM`, `-m⁻¹ mod 2⁶⁴` in `r0` and `u = t₀ (-m⁻¹) mod
2⁶⁴`, if `T + u m` fits in `w + 2` words. -/
theorem montRedPass_ok {s : State} {B : Addr} {Z dA dM w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h10 : s.gpr .r10 = off B dM) (h3 : s.gpr .r3 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 2) ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dM)
    (hinv : ((word s.mem B dM).toNat * (s.gpr .r0).toNat + 1) % 2 ^ 64 = 0)
    (hfit : ∀ u < 2 ^ 64, wordsVal s.mem B dA (w + 2) + u * wordsVal s.mem B dM w < 2 ^ (64 * (w + 2))) :
    WP isa montRedPass s fun s' =>
      (Outside B dA (8 * (w + 2)) s.mem s'.mem ∧
        2 ^ 64 * wordsVal s'.mem B dA (w + 1) = wordsVal s.mem B dA (w + 2) +
          (word s.mem B dA).toNat * (s.gpr .r0).toNat % 2 ^ 64 * wordsVal s.mem B dM w) ∧
      Keep montRedRegs s s' := by
  have hnw := hs.nowrap
  unfold montRedPass
  refine WP.seq (WP.mono (montRedHead_ok hs h8 h10 h3 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    hinv) fun s₁ ⟨⟨i17, i18, i14, i15, i16, im⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (montMacLoop_ok (k := 8) (N := w - 1) (hs.congr k₁.wr) (.inr rfl) i14 i15 i16 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨j14, jout, jeq, k₂⟩ => ?_)
  refine WP.mono (montRedTop_ok (hs.congr (k₁.trans k₂).wr) j14 (by omega_arith)) fun s₃ ⟨jm, k₃⟩ => ?_
  have k23 := k₂.trans k₃
  -- The top words read are those on entry.
  have wt : word s₂.mem B (dA + 8 * (w - 1) + 8) = word s.mem B (dA + 8 * w) := by
    rw [jout.word (by omega_arith) (by omega_arith), im, show dA + 8 * (w - 1) + 8 = dA + 8 * w by omega_arith]
  have wt' : word s₂.mem B (dA + 8 * (w - 1) + 16) = word s.mem B (dA + 8 * w + 8) := by
    rw [jout.word (by omega_arith) (by omega_arith), im, show dA + 8 * (w - 1) + 16 = dA + 8 * w + 8 by omega_arith]
  rw [im] at jeq
  -- The values: `L` the low words stored, `c` the carry, `u` the multiple.
  generalize hu : (s₁.gpr .r17).toNat = u at jeq i18 i17
  generalize hc₀ : (s₁.gpr .r18).toNat = c₀ at jeq i18
  generalize hc : (s₂.gpr .r18).toNat = c at jeq jm
  generalize hX : (word s.mem B (dA + 8 * w)).toNat = X at wt
  generalize hY : (word s.mem B (dA + 8 * w + 8)).toNat = Y at wt'
  have eA : wordsVal s.mem B dA (w + 2) = (word s.mem B dA).toNat + 2 ^ 64 * wordsVal s.mem B (dA + 8) (w - 1) +
      2 ^ (64 * w) * (X + 2 ^ 64 * Y) := by
    rw [← hX, ← hY, show w + 2 = w + 1 + 1 from rfl, wordsVal_succ_top, wordsVal_succ_top,
      show w = w - 1 + 1 by omega_arith, wordsVal, show w - 1 + 1 - 1 = w - 1 by omega_arith,
      show dA + 8 * (w - 1 + 1) = dA + 8 * w by omega_arith, show 64 * (w - 1 + 1 + 1) = 64 * w + 64 by omega_arith,
      show 64 * (w - 1 + 1) = 64 * w by omega_arith, Nat.pow_add]
    grind
  have eM : wordsVal s.mem B dM w = (word s.mem B dM).toNat + 2 ^ 64 * wordsVal s.mem B (dM + 8) (w - 1) := by
    rw [show w = w - 1 + 1 by omega_arith, wordsVal, show w - 1 + 1 - 1 = w - 1 by omega_arith]
  have p64 : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega_arith
  -- The top fits.
  have hsum := mont_red_sum (X := X) (Y := Y) (m0 := (word s.mem B dM).toNat) p64 i18 jeq
  rw [← eA, ← eM] at hsum
  have hb := hfit u (by rw [← hu]; exact (s₁.gpr .r17).isLt)
  have htop : X + c + 2 ^ 64 * Y < 2 ^ 128 := by
    have : 2 ^ (64 * w) * (X + c + 2 ^ 64 * Y) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega_arith]; omega_using [hsum, hb]
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨⟨?_, ?_⟩, (k₁.trans k23).mono (by decide)⟩
  · rw [jm, ← im]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      (((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))
  · have hXl : X < 2 ^ 64 := hX ▸ (word s.mem B _).isLt
    have hcl : c < 2 ^ 64 := hc ▸ (s₂.gpr .r18).isLt
    rw [jm, show w + 1 = w - 1 + 2 by omega_arith, mont_wordsVal_write2 _ _ _ _ _ _ (by omega_arith), wt, wt', hX, hY,
      mont_toNat_ofNat_top hXl hcl htop, ← i17, hsum, Nat.mul_add, ← Nat.mul_assoc, p64]

end VG.Proof.Bignum.PPC64LE
