module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtCorr
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the digit loop's invariant, apart from the step's pieces

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root's digit loop

At count `c`, after `h - c` digits of `X'` (`2 h` words): the remainder in
place of `X'`'s top `2 (h - c)` words and `D = 2 s β^c` for the root `s` of
those words (`SqI`); a step keeps it with `c - 1` (`stepX_ok`), and the loop
ends at `c = 0` with the root of `X'` (`sqLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (isqrt)

/-! ## Words and windows -/

/-- `L` words from word `k` of `N`. -/
theorem wv_window (m : Mem) (B : Addr) (d : Nat) {k L N : Nat} (h : k + L ≤ N) :
    wv m B (d + 8 * k) L = wv m B d N / 2 ^ (64 * k) % 2 ^ (64 * L) := by
  rw [wv_div_pow m B d (show k ≤ N by omega), wv_mod_low m B (d + 8 * k) (show L ≤ N - k by omega)]

/-- `a + P b = c + P d` with `a, c < P`: `a = c` and `b = d`. -/
theorem lo_hi_eq {P a b c d : Nat} (ha : a < P) (hc : c < P) (h : a + P * b = c + P * d) : a = c ∧ b = d := by
  have hP : 0 < P := by omega
  have m1 := Nat.add_mul_mod_self_left a P b
  have m2 := Nat.add_mul_mod_self_left c P d
  have d1 := Nat.add_mul_div_left a b hP
  have d2 := Nat.add_mul_div_left c d hP
  rw [Nat.mod_eq_of_lt ha] at m1
  rw [Nat.mod_eq_of_lt hc] at m2
  rw [Nat.div_eq_of_lt ha, Nat.zero_add] at d1
  rw [Nat.div_eq_of_lt hc, Nat.zero_add] at d2
  rw [h] at m1 d1
  exact ⟨m1.symm.trans m2, d1.symm.trans d2⟩

/-- A number whose window at word `k` of `L` words is replaced: the low part
stays, the window is the new one, and the words above it stay zero. -/
theorem wv_replace {m m' : Mem} {B : Addr} {d k L N lo R R' : Nat} (hkN : k + L ≤ N)
    (hm : wv m B d N = lo + 2 ^ (64 * k) * R) (hlo : lo < 2 ^ (64 * k))
    (hR : R < 2 ^ (64 * L)) (lo' : wv m' B d k = wv m B d k)
    (hi' : wv m' B (d + 8 * (k + L)) (N - (k + L)) = wv m B (d + 8 * (k + L)) (N - (k + L)))
    (hR' : wv m' B (d + 8 * k) L = R') :
    wv m' B d N = lo + 2 ^ (64 * k) * R' := by
  have split : ∀ (mm : Mem), wv mm B d N = wv mm B d k + 2 ^ (64 * k) * wv mm B (d + 8 * k) L +
      2 ^ (64 * k) * 2 ^ (64 * L) * wv mm B (d + 8 * (k + L)) (N - (k + L)) := fun mm => by
    rw [show N = k + (L + (N - (k + L))) by omega, wv_add, wv_add, show k + (L + (N - (k + L))) - (k + L) =
      N - (k + L) by omega, show d + 8 * k + 8 * L = d + 8 * (k + L) by omega]
    grind
  have e1 := split m
  have e2 := split m'
  have hlok := wv_lt m B d k
  have hwin := wv_lt m B (d + 8 * k) L
  -- The low part is `lo`, the window `R`, and the high part zero.
  have hP := Nat.two_pow_pos (64 * k)
  have hPL := Nat.two_pow_pos (64 * L)
  rw [hm, Nat.add_assoc, show 2 ^ (64 * k) * wv m B (d + 8 * k) L + 2 ^ (64 * k) * 2 ^ (64 * L) *
      wv m B (d + 8 * (k + L)) (N - (k + L)) = 2 ^ (64 * k) * (wv m B (d + 8 * k) L + 2 ^ (64 * L) *
      wv m B (d + 8 * (k + L)) (N - (k + L))) by grind] at e1
  have h1 := lo_hi_eq hlo hlok e1
  obtain ⟨hl, hr⟩ := h1
  have hz : wv m B (d + 8 * (k + L)) (N - (k + L)) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (d + 8 * (k + L)) (N - (k + L))) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * L) ≤ 2 ^ (64 * L) * wv m B (d + 8 * (k + L)) (N - (k + L)) := Nat.le_mul_of_pos_right _ h0
      omega
  rw [e2, lo', hi', hz, hR', ← hl]
  simp

/-- A word of `X / 2`, from two of `X`'s. -/
theorem half_digit (X k : Nat) :
    X / 2 ^ (64 * (k + 1)) % 2 ^ 64 % 2 * 2 ^ 63 + X / 2 ^ (64 * k) % 2 ^ 64 / 2 = X / 2 / 2 ^ (64 * k) % 2 ^ 64 := by
  have e : X / 2 ^ (64 * (k + 1)) = X / 2 ^ (64 * k) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  have e2 : X / 2 / 2 ^ (64 * k) = X / 2 ^ (64 * k) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [e, e2]
  generalize X / 2 ^ (64 * k) = Y
  have := Nat.div_add_mod Y (2 ^ 64)
  generalize Y / 2 ^ 64 = a at this ⊢
  generalize hb : Y % 2 ^ 64 = b at this ⊢
  have hb' : b < 2 ^ 64 := by rw [← hb]; exact Nat.mod_lt _ (by decide)
  subst this
  omega

/-- Half of a number's word `k`, from its words `k` and `k + 1`. -/
theorem hv_word (m : Mem) (B : Addr) (ed w : Nat) {V k : Nat} (hk : k + 1 < w) (hV : wv m B ed w = V) :
    (hv (word m B (ed + 8 * (k + 1))) (word m B (ed + 8 * k))).toNat = V / 2 / 2 ^ (64 * k) % 2 ^ 64 := by
  rw [hv_toNat, word_of_wv m B ed w hk, word_of_wv m B ed w (show k < w by omega), hV, half_digit]

/-- A number below `β³` from its three words. -/
theorem words3 {X : Nat} (h : X < 2 ^ 64 * 2 ^ 64 * 2 ^ 64) :
    X = X / (2 ^ 64 * 2 ^ 64) % 2 ^ 64 * (2 ^ 64 * 2 ^ 64) + X / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 + X % 2 ^ 64 := by
  omega

/-- The root of `x / b²` is that of `x`, shifted down by `b`. -/
theorem isqrt_div (x b : Nat) (hb : 0 < b) : isqrt (x / (b * b)) = isqrt x / b := by
  have lo := VG.Proof.Rsa.RecoverDet.isqrt_sq_le x
  have hi := VG.Proof.Rsa.RecoverDet.lt_succ_isqrt_sq x
  generalize isqrt x = s at lo hi
  have t1 : s / b * b ≤ s := Nat.div_mul_le_self s b
  have t2 : s < (s / b + 1) * b := by
    have := Nat.lt_div_mul_add (a := s) hb; rw [Nat.add_mul, Nat.one_mul]; exact this
  generalize s / b = t at t1 t2
  have hbb : 0 < b * b := Nat.mul_pos hb hb
  refine VG.Proof.Rsa.RecoverDet.isqrt_eq ?_ ?_
  · rw [Nat.le_div_iff_mul_le hbb]
    calc t * t * (b * b) = t * b * (t * b) := by grind
      _ ≤ s * s := Nat.mul_le_mul t1 t1
      _ ≤ x := lo
  · rw [Nat.div_lt_iff_lt_mul hbb]
    calc x < (s + 1) * (s + 1) := hi
      _ ≤ (t + 1) * b * ((t + 1) * b) := Nat.mul_le_mul (by omega) (by omega)
      _ = (t + 1) * (t + 1) * (b * b) := by grind

/-- `X`'s low `2 c` words from its low `2 (c - 1)` and the pair above them. -/
theorem mod_pair (X m : Nat) :
    X % 2 ^ (64 * (2 * (m + 1))) = X % 2 ^ (64 * (2 * m)) + 2 ^ (64 * (2 * m)) * (X / 2 ^ (64 * (2 * m)) % (2 ^ 64 * 2 ^ 64)) := by
  rw [show 2 ^ (64 * (2 * (m + 1))) = 2 ^ (64 * (2 * m)) * (2 ^ 64 * 2 ^ 64) by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1, Nat.mod_mul]

/-- `X`'s top words from those of one pair fewer: `A β² + P`. -/
theorem div_pair (X m : Nat) :
    X / 2 ^ (64 * (2 * m)) = X / 2 ^ (64 * (2 * (m + 1))) * (2 ^ 64 * 2 ^ 64) + X / 2 ^ (64 * (2 * m)) % (2 ^ 64 * 2 ^ 64) := by
  rw [show 2 ^ (64 * (2 * (m + 1))) = 2 ^ (64 * (2 * m)) * (2 ^ 64 * 2 ^ 64) by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ _).symm

/-- A sequence of seven, its last two split off. -/
theorem seq7 {M : ISA} {a b c d e f g : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.seq a (.seq b (.seq c (.seq d (.seq e f))))) s fun t => WP M g t Q) :
    WP M (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) s Q := by
  simp only [WP.seq_iff] at h ⊢; exact h

/-! ## The loop's invariant -/

/-- What the digit loop changes: arrays `sqS` (1), `sqD` (3), `sqU` (5) and
`sqZ` (7), the count and `sU`. -/
def SqLP (W y : Nat) : Prop :=
  (slot W sqS ≤ y ∧ y < slot W sqS + 8 * (W + 2)) ∨ (slot W sqD ≤ y ∧ y < slot W sqD + 8 * (W + 2)) ∨
  (slot W sqU ≤ y ∧ y < slot W sqU + 8 * (W + 2)) ∨ (slot W sqZ ≤ y ∧ y < slot W sqZ + 8 * (W + 2)) ∨
  (8 * sCt ≤ y ∧ y < 8 * sCt + 8) ∨ (8 * sU ≤ y ∧ y < 8 * sU + 8)

/-- `X`'s top words above its low `2 c`. -/
abbrev Ap (X c : Nat) : Nat := X / 2 ^ (64 * (2 * c))

/-- At count `c`: the remainder of `X`'s top words `A = Ap X c` in place of
them, `D = 2 isqrt(A) β^c`, and the reciprocal of the first digit. -/
structure SqI (s₀ : State) (B : Addr) (Z W h X : Nat) (c : Nat) (t : State) : Prop where
  ws : Ws t B Z W
  ct : word t.mem B (8 * sCt) = BitVec.ofNat 64 c
  z : wv t.mem B (slot W sqZ) W =
    X % 2 ^ (64 * (2 * c)) + (Ap X c - isqrt (Ap X c) * isqrt (Ap X c)) * 2 ^ (64 * (2 * c))
  d : wv t.mem B (slot W sqD) W = 2 * isqrt (Ap X c) * 2 ^ (64 * c)
  v : (word t.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / isqrt (Ap X (h - 1)) - 2 ^ 64
  frm : FrmP B (SqLP W) s₀.mem t.mem
  keep : Keep mmRegs s₀ t
  dtop : word t.mem B (slot W sqD + 8 * W) = 0

/-- The digit step's numbers at count `c` (`1 ≤ c < h`): the root `s` of
`A = Ap X c` (`2 j` words, `j = h - c`, its top word normalized), and its
bounds. -/
theorem root_bounds {h X c : Nat} (hX : X < 2 ^ (64 * (2 * h))) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X)
    (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) :
    2 ^ 63 * 2 ^ (64 * (h - c - 1)) ≤ isqrt (Ap X c) ∧ isqrt (Ap X c) < 2 ^ 64 * 2 ^ (64 * (h - c - 1)) := by
  have hA1 : Ap X c < 2 ^ (64 * (h - c)) * 2 ^ (64 * (h - c)) := by
    unfold Ap
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega))
  have hA0 : 2 ^ 63 * 2 ^ (64 * (h - c - 1)) * (2 ^ 63 * 2 ^ (64 * (h - c - 1))) ≤ Ap X c := by
    unfold Ap
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    refine Nat.le_trans (Nat.le_of_eq ?_) hXt
    rw [show 2 ^ 63 * 2 ^ (64 * (h - c - 1)) * (2 ^ 63 * 2 ^ (64 * (h - c - 1))) * 2 ^ (64 * (2 * c)) =
      2 ^ (63 + 64 * (h - c - 1) + (63 + 64 * (h - c - 1)) + 64 * (2 * c)) by simp only [Nat.pow_add]]
    rw [show 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) = 2 ^ (62 + 64 * (2 * h - 1)) by rw [Nat.pow_add]]
    congr 1; omega
  constructor
  · exact (sq_le_iff _ _).mp hA0
  · refine Nat.lt_of_not_le fun hc => ?_
    have := Nat.mul_le_mul hc hc
    rw [show 2 ^ 64 * 2 ^ (64 * (h - c - 1)) = 2 ^ (64 * (h - c)) by rw [← Nat.pow_add]; congr 1; omega] at this
    have := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (Ap X c)
    omega

/-- The offsets a digit step changes are the loop's. -/
theorem stepP_sqLP {W h c y : Nat} (hwh : W = 2 * h + 4) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h)
    (hy : ((slot W sqU ≤ y ∧ y < slot W sqU + 24) ∨ (slot W sqS + 8 ≤ y ∧ y < slot W sqS + 24) ∨
      (208 ≤ y ∧ y < 216)) ∨ ((slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
        (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) ∨ (200 ≤ y ∧ y < 208)) : SqLP W y := by
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have sU' : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have sS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have hsU : 8 * sU = 208 := rfl
  have hsCt : 8 * sCt = 200 := rfl
  unfold SqLP
  rcases hy with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact .inr (.inr (.inl ⟨by omega, by omega⟩))
  · exact .inl ⟨by omega, by omega⟩
  · exact .inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  · exact .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  · exact .inr (.inl ⟨by omega, by omega⟩)
  · exact .inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))

/-- A digit step's program at count `c`: from the window `R` and `D = Y`, the
estimate's operands `N` and `D'` and the digit `q`, the window becomes
`R - (Y + q) q` and `D` becomes `Y + 2 q`. -/
theorem stepW_ok {t : State} {B : Addr} {Z W h c R Y N Dd q : Nat} (hw : Ws t B Z W) (hwh : W = 2 * h + 4)
    (hct : word t.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h)
    (hRw : wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R)
    (hYw : wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y)
    (hY0 : word t.mem B (slot W sqD + 8 * (c - 1)) = 0)
    (hy1 : (word t.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat + 2 ≤ 2 ^ 64)
    (hN : R / 2 / 2 ^ (64 * (h - c - 1)) = N) (hDd : Y / 2 / 2 ^ (64 * (h - c - 1)) = Dd)
    (hN3 : N < 2 ^ 64 * 2 ^ 64 * 2 ^ 64) (hd1 : 2 ^ 63 ≤ Dd / 2 ^ 64) (hDβ : Dd < 2 ^ 64 * 2 ^ 64)
    (hNu : N / (2 ^ 64 * 2 ^ 64) ≤ Dd / 2 ^ 64) (hUD : N < (2 ^ 64 + 1) * Dd)
    (hq1 : q ≤ min (N / Dd) (2 ^ 64 - 1)) (hq2 : min (N / Dd) (2 ^ 64 - 1) ≤ q + 2)
    (lo : (Y + q) * q ≤ R) (hi : R < (Y + (q + 1)) * (q + 1)) (hqβ : q < 2 ^ 64)
    (hR2 : 2 * R < 2 ^ (64 * (h - (c - 1) + 2))) (hB : 2 * ((Y + (q + 2)) * (q + 2)) < 2 ^ (64 * (h - (c - 1) + 2)))
    (hv0 : (word t.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / (Dd / 2 ^ 64) - 2 ^ 64) :
    WP isa stepX t fun t₃ => t₃.zf = some (decide (c = 1)) ∧ word t₃.mem B (8 * sCt) = BitVec.ofNat 64 (c - 1) ∧
      wv t₃.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R - (Y + q) * q ∧
      wv t₃.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y + 2 * q ∧
      FrmP B (fun y => ((slot W sqU ≤ y ∧ y < slot W sqU + 24) ∨ (slot W sqS + 8 ≤ y ∧ y < slot W sqS + 24) ∨
      (208 ≤ y ∧ y < 216)) ∨ ((slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
        (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) ∨ (200 ≤ y ∧ y < 208)) t.mem t₃.mem ∧
      Keep mmRegs t t₃ ∧ Ws t₃ B Z W := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have sU' : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have sS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have eL4 : h - (c - 1) + 2 - 4 = h - c - 1 := by omega
  -- The estimate's words: `N`'s three and `D'`'s two.
  have hu0 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 4 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 4)))).toNat = N % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, eL4, hN]
  have hu1 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 3 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 3)))).toNat = N / 2 ^ 64 % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, show h - (c - 1) + 2 - 3 = h - c - 1 + 1 by omega,
      pow64_succ, ← Nat.div_div_eq_div_mul, hN]
  have hu2 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 2 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 2)))).toNat =
      N / (2 ^ 64 * 2 ^ 64) % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, show h - (c - 1) + 2 - 2 = h - c - 1 + 1 + 1 by omega,
      pow64_succ, pow64_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hN, Nat.div_div_eq_div_mul]
  have hdv0 : (hv (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 4 + 1)))
      (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 4)))).toNat = Dd % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hYw, eL4, hDd]
  have hDβ' : Dd / 2 ^ 64 < 2 ^ 64 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hDβ
  have hdv1 : (hv (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 3 + 1)))
      (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 3)))).toNat = Dd / 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hYw, show h - (c - 1) + 2 - 3 = h - c - 1 + 1 by omega,
      pow64_succ, ← Nat.div_div_eq_div_mul, hDd, Nat.mod_eq_of_lt hDβ']
  have hNs : N / (2 ^ 64 * 2 ^ 64) % 2 ^ 64 * 2 ^ 128 + N / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 + N % 2 ^ 64 = N := by
    rw [pow128]; exact (words3 hN3).symm
  have hDs : Dd / 2 ^ 64 * 2 ^ 64 + Dd % 2 ^ 64 = Dd := Nat.div_add_mod' _ _
  have hNβ : N / (2 ^ 64 * 2 ^ 64) < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.mul_comm] at hN3; exact hN3
  have hsU : 8 * sU = 208 := rfl
  have hsCt : 8 * sCt = 200 := rfl
  -- The estimate.
  show WP isa (.seq (.block estX) (.seq mulSubX (.seq (.block toE) (.seq fixX (.seq fixX (.seq fixX
    (.seq (.block updX) (.block countNext)))))))) t _
  refine WP.seq (WP.mono (estX_ok hw hwh hct hc1 hch rfl rfl rfl rfl rfl rfl rfl rfl
    (by rw [hdv1]; exact hd1) (by rw [hdv1]; exact hv0) (by rw [hu2, hdv1, Nat.mod_eq_of_lt hNβ]; exact hNu)
    (by rw [hu0, hu1, hu2, hdv0, hdv1, hNs, hDs]; exact hUD)) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  rw [hu0, hu1, hu2, hdv0, hdv1, hNs, hDs] at hm₁
  have FP₁ : FrmP B (fun y => (slot W sqU ≤ y ∧ y < slot W sqU + 24) ∨ (slot W sqS + 8 ≤ y ∧ y < slot W sqS + 24) ∨
      (208 ≤ y ∧ y < 216)) t.mem t₁.mem := by
    intro x hx
    rw [hm₁, writeW_outside _ B _ (d := 8 * sU) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqS + 8 * 2) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqS + 8 * 1) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU + 8 * 2) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU + 8 * 1) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU) (by omega) x (by omega)]
  have hw₁ := hw.congrP FP₁ (fun y hy => by unfold DOk; omega) k₁ (by decide)
  have ct₁ : word t₁.mem B (8 * sCt) = BitVec.ofNat 64 c := by
    rw [FP₁.word_eq (fun y h1 h2 hy => by omega) (by omega), hct]
  have hR₁ : wv t₁.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R := by
    rw [FP₁.wv_eq (fun y h1 h2 hy => by omega) (by omega), hRw]
  have hY₁ : wv t₁.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y := by
    rw [FP₁.wv_eq (fun y h1 h2 hy => by omega) (by omega), hYw]
  have hY0₁ : word t₁.mem B (slot W sqD + 8 * (c - 1)) = 0 := by
    rw [FP₁.word_eq (fun y h1 h2 hy => by omega) (by omega), hY0]
  have hy1₁ : (word t₁.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat + 2 ≤ 2 ^ 64 := by
    rw [FP₁.word_eq (fun y h1 h2 hy => by omega) (by omega)]; exact hy1
  have hqh : word t₁.mem B (8 * sU) = BitVec.ofNat 64 (min (N / Dd) (2 ^ 64 - 1)) := by
    rw [hm₁, word_writeW_self]
  -- The subtraction and the corrections, then the count.
  refine seq7 (WP.mono (corr_ok hw₁ hwh ct₁ hc1 hch hR₁ hY₁ hY0₁ hy1₁ hqh (by omega) hqβ lo hi hq1 hq2 hR2 hB) fun t₂ ⟨hz₂, hd₂, FP₂, k₂, hw₂⟩ => ?_)
  have ct₂ : word t₂.mem B (8 * sCt) = BitVec.ofNat 64 c := by
    rw [FP₂.word_eq (fun y h1 h2 hy => by omega) (by omega), ct₁]
  refine WP.mono (countNext_ok hw₂ ct₂ hc1 (by omega)) fun t₃ ⟨hzf, hm₃, k₃⟩ => ⟨hzf, ?_⟩
  have FP₃ : FrmP B (fun y => 200 ≤ y ∧ y < 208) t₂.mem t₃.mem := by
    rw [hm₃]; exact FrmP.of_writeW _ (by omega) fun y h1 h2 => by omega
  have FP : FrmP B (fun y => ((slot W sqU ≤ y ∧ y < slot W sqU + 24) ∨ (slot W sqS + 8 ≤ y ∧ y < slot W sqS + 24) ∨
      (208 ≤ y ∧ y < 216)) ∨ ((slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
        (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) ∨ (200 ≤ y ∧ y < 208)) t.mem t₃.mem :=
    ((FP₁.mono fun y hy => .inl hy).trans (FP₂.mono fun y hy => .inr (.inl hy))).trans
      (FP₃.mono fun y hy => .inr (.inr hy))
  refine ⟨by rw [hm₃, word_writeW_self], ?_, ?_, FP, ((k₁.trans k₂).trans k₃).mono (by decide),
    hw.congrP FP (fun y hy => by unfold DOk; omega) ((k₁.trans k₂).trans k₃) (by decide)⟩
  · rw [FP₃.wv_eq (fun y h1 h2 hy => by omega) (by omega), hz₂]
  · rw [FP₃.wv_eq (fun y h1 h2 hy => by omega) (by omega), hd₂]

/-- The estimate alone, for what the steps after it need: the working space and the count. -/
theorem est_ok {t : State} {B : Addr} {Z W h c R Y N Dd : Nat} (hw : Ws t B Z W) (hwh : W = 2 * h + 4)
    (hct : word t.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h)
    (hRw : wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R)
    (hYw : wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y)
    (hN : R / 2 / 2 ^ (64 * (h - c - 1)) = N) (hDd : Y / 2 / 2 ^ (64 * (h - c - 1)) = Dd)
    (hN3 : N < 2 ^ 64 * 2 ^ 64 * 2 ^ 64) (hd1 : 2 ^ 63 ≤ Dd / 2 ^ 64) (hDβ : Dd < 2 ^ 64 * 2 ^ 64)
    (hNu : N / (2 ^ 64 * 2 ^ 64) ≤ Dd / 2 ^ 64) (hUD : N < (2 ^ 64 + 1) * Dd)
    (hv0 : (word t.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / (Dd / 2 ^ 64) - 2 ^ 64) :
    WP isa (.block estX) t fun t₁ => Ws t₁ B Z W ∧ word t₁.mem B (8 * sCt) = BitVec.ofNat 64 c := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have sU' : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have sS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have eL4 : h - (c - 1) + 2 - 4 = h - c - 1 := by omega
  have hu0 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 4 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 4)))).toNat = N % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, eL4, hN]
  have hu1 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 3 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 3)))).toNat = N / 2 ^ 64 % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, show h - (c - 1) + 2 - 3 = h - c - 1 + 1 by omega,
      pow64_succ, ← Nat.div_div_eq_div_mul, hN]
  have hu2 : (hv (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 2 + 1)))
      (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 2)))).toNat =
      N / (2 ^ 64 * 2 ^ 64) % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hRw, show h - (c - 1) + 2 - 2 = h - c - 1 + 1 + 1 by omega,
      pow64_succ, pow64_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hN, Nat.div_div_eq_div_mul]
  have hdv0 : (hv (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 4 + 1)))
      (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 4)))).toNat = Dd % 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hYw, eL4, hDd]
  have hDβ' : Dd / 2 ^ 64 < 2 ^ 64 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hDβ
  have hdv1 : (hv (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 3 + 1)))
      (word t.mem B (slot W sqD + 8 * (c - 1) + 8 * (h - (c - 1) + 2 - 3)))).toNat = Dd / 2 ^ 64 := by
    rw [hv_word t.mem B _ (h - (c - 1) + 2) (by omega) hYw, show h - (c - 1) + 2 - 3 = h - c - 1 + 1 by omega,
      pow64_succ, ← Nat.div_div_eq_div_mul, hDd, Nat.mod_eq_of_lt hDβ']
  have hNs : N / (2 ^ 64 * 2 ^ 64) % 2 ^ 64 * 2 ^ 128 + N / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 + N % 2 ^ 64 = N := by
    rw [pow128]; exact (words3 hN3).symm
  have hDs : Dd / 2 ^ 64 * 2 ^ 64 + Dd % 2 ^ 64 = Dd := Nat.div_add_mod' _ _
  have hNβ : N / (2 ^ 64 * 2 ^ 64) < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.mul_comm] at hN3; exact hN3
  have hsU : 8 * sU = 208 := rfl
  have hsCt : 8 * sCt = 200 := rfl
  refine WP.mono (estX_ok hw hwh hct hc1 hch rfl rfl rfl rfl rfl rfl rfl rfl
    (by rw [hdv1]; exact hd1) (by rw [hdv1]; exact hv0) (by rw [hu2, hdv1, Nat.mod_eq_of_lt hNβ]; exact hNu)
    (by rw [hu0, hu1, hu2, hdv0, hdv1, hNs, hDs]; exact hUD)) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have FP₁ : FrmP B (fun y => (slot W sqU ≤ y ∧ y < slot W sqU + 24) ∨ (slot W sqS + 8 ≤ y ∧ y < slot W sqS + 24) ∨
      (208 ≤ y ∧ y < 216)) t.mem t₁.mem := by
    intro x hx
    rw [hm₁, writeW_outside _ B _ (d := 8 * sU) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqS + 8 * 2) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqS + 8 * 1) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU + 8 * 2) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU + 8 * 1) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqU) (by omega) x (by omega)]
  exact ⟨hw.congrP FP₁ (fun y hy => by unfold DOk; omega) k₁ (by decide),
    by rw [FP₁.word_eq (fun y h1 h2 hy => by omega) (by omega), hct]⟩

/-- A digit step at count `c` (`1 ≤ c < h`), and its estimate alone. -/
theorem stepXE_ok {s₀ t : State} {B : Addr} {Z W h X c : Nat} (hwh : W = 2 * h + 4) (hh : h ≤ 128)
    (hX : X < 2 ^ (64 * (2 * h))) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X)
    (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) (hI : SqI s₀ B Z W h X c t) :
    (WP isa stepX t fun t' => t'.zf = some (decide (c = 1)) ∧ SqI s₀ B Z W h X (c - 1) t') ∧
    WP isa (.block estX) t fun t₁ => Ws t₁ B Z W ∧ word t₁.mem B (8 * sCt) = BitVec.ofNat 64 c := by
  have hw := hI.ws
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have sU' : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have sS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  -- The numbers: `A = Ap X c`, its root `s` and remainder `r`, the next pair `P`, the window `R`.
  obtain ⟨hs1, hs2⟩ := root_bounds hX hXt hc1 hch
  obtain ⟨lo0, hi0⟩ := VG.Proof.Rsa.RecoverDet.isqrt_spec (Ap X c)
  generalize hA : Ap X c = A at hs1 hs2 lo0 hi0
  generalize hs : isqrt A = s at hs1 hs2 lo0 hi0
  have e1 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by grind
  generalize hr : A - s * s = r
  have hr2 : r ≤ 2 * s := by omega
  generalize hP : X / 2 ^ (64 * (2 * (c - 1))) % (2 ^ 64 * 2 ^ 64) = P
  have hPβ : P < 2 ^ 64 * 2 ^ 64 := by rw [← hP]; exact Nat.mod_lt _ (by decide)
  -- Powers: `Pm = β^(2 (c - 1))`, `Pc = β^(c - 1)`, `Pj = β^(h - c - 1)`.
  have eL : h - (c - 1) + 2 = (h - c - 1) + 4 := by omega
  have pL : 2 ^ (64 * (h - (c - 1) + 2)) = 2 ^ 64 * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) * 2 ^ (64 * (h - c - 1)) := by
    rw [eL, show 64 * (h - c - 1 + 4) = 64 + 64 + (64 + 64) + 64 * (h - c - 1) by omega]
    simp only [Nat.pow_add]
  have p2c : 2 ^ (64 * (2 * c)) = 2 ^ (64 * (2 * (c - 1))) * (2 ^ 64 * 2 ^ 64) := by
    rw [show 64 * (2 * c) = 64 * (2 * (c - 1)) + 64 + 64 by omega, Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
  have pc : 2 ^ (64 * c) = 2 ^ (64 * (c - 1)) * 2 ^ 64 := by
    rw [show 64 * c = 64 * (c - 1) + 64 by omega, Nat.pow_add]
  have hPm := Nat.two_pow_pos (64 * (2 * (c - 1)))
  have hPc := Nat.two_pow_pos (64 * (c - 1))
  have hPj := Nat.two_pow_pos (64 * (h - c - 1))
  generalize hR : r * (2 ^ 64 * 2 ^ 64) + P = R
  -- `R < β^L / 2`.
  have hR2 : 2 * R < 2 ^ (64 * (h - (c - 1) + 2)) := by
    rw [pL, ← hR]
    have : r * (2 ^ 64 * 2 ^ 64) ≤ 2 * s * (2 ^ 64 * 2 ^ 64) := Nat.mul_le_mul_right _ hr2
    have : s * (2 ^ 64 * 2 ^ 64) < 2 ^ 64 * 2 ^ (64 * (h - c - 1)) * (2 ^ 64 * 2 ^ 64) :=
      Nat.mul_lt_mul_of_pos_right hs2 (by decide)
    have : 1 ≤ 2 ^ (64 * (h - c - 1)) := hPj
    have e : 2 ^ 64 * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) * 2 ^ (64 * (h - c - 1)) =
      2 ^ 64 * (2 ^ 64 * 2 ^ (64 * (h - c - 1)) * (2 ^ 64 * 2 ^ 64)) := by grind
    have : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * (h - c - 1)) * (2 ^ 64 * 2 ^ 64) := by
      have := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ 64) (Nat.mul_le_mul_left (2 ^ 64) this)
      grind
    omega
  -- The window: `R`.
  have hz := hI.z
  rw [hA, hs, hr] at hz
  have hZw : wv t.mem B (slot W sqZ) W =
      X % 2 ^ (64 * (2 * (c - 1))) + 2 ^ (64 * (2 * (c - 1))) * R := by
    have mp := mod_pair X (c - 1)
    rw [show c - 1 + 1 = c by omega, hP] at mp
    rw [hz, mp, p2c, ← hR]
    grind
  have hXm : X % 2 ^ (64 * (2 * (c - 1))) < 2 ^ (64 * (2 * (c - 1))) := Nat.mod_lt _ hPm
  have hRL : R < 2 ^ (64 * (h - (c - 1) + 2)) := by omega
  have hRw : wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R := by
    rw [show slot W sqZ + 16 * (c - 1) = slot W sqZ + 8 * (2 * (c - 1)) by omega,
      wv_window _ _ _ (show 2 * (c - 1) + (h - (c - 1) + 2) ≤ W by omega), hZw,
      Nat.add_mul_div_left _ _ hPm, Nat.div_eq_of_lt hXm, Nat.zero_add, Nat.mod_eq_of_lt hRL]
  -- `D`'s window: `Y = 2 s β`.
  generalize hY : 2 * s * 2 ^ 64 = Y
  have hYL : Y < 2 ^ (64 * (h - (c - 1) + 2)) := by
    rw [pL, ← hY]
    have : 2 * s * 2 ^ 64 < 2 * (2 ^ 64 * 2 ^ (64 * (h - c - 1))) * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by decide)
    have : 2 * (2 ^ 64 * 2 ^ (64 * (h - c - 1))) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) * 2 ^ (64 * (h - c - 1)) := by
      have : 2 * 2 ^ 64 ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ 64) := by decide
      have := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ (64 * (h - c - 1))) this
      grind
    omega
  have hD := hI.d
  rw [hA, hs] at hD
  have hYw : wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y := by
    rw [wv_window _ _ _ (show (c - 1) + (h - (c - 1) + 2) ≤ W by omega), hD, pc,
      show 2 * s * (2 ^ (64 * (c - 1)) * 2 ^ 64) = Y * 2 ^ (64 * (c - 1)) by rw [← hY]; grind,
      Nat.mul_div_cancel _ hPc, Nat.mod_eq_of_lt hYL]
  have hY0 : word t.mem B (slot W sqD + 8 * (c - 1)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    have := word_of_wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) (q := 0) (by omega)
    rw [Nat.mul_zero, Nat.add_zero, hYw, Nat.pow_zero, Nat.div_one, ← hY] at this
    rw [this]; simp
  have hY1 : (word t.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat = 2 * s % 2 ^ 64 := by
    have := word_of_wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) (q := 1) (by omega)
    rw [hYw, Nat.mul_one, Nat.mul_one, ← hY, Nat.mul_div_cancel _ (by decide)] at this
    exact this
  have hy1 : (word t.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat + 2 ≤ 2 ^ 64 := by rw [hY1]; omega
  -- The estimate's bounds.
  have eL4 : h - (c - 1) + 2 - 4 = h - c - 1 := by omega
  have hK1 : 2 ^ (64 * (h - c - 1)) = 1 ∨ 2 ^ 64 ≤ 2 ^ (64 * (h - c - 1)) := by
    rcases Nat.eq_zero_or_pos (h - c - 1) with h0 | h0
    · left; rw [h0, Nat.mul_zero, Nat.pow_zero]
    · right; exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨N, hN⟩ : ∃ N, R / 2 / 2 ^ (64 * (h - c - 1)) = N := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ Dd, s * 2 ^ 64 / 2 ^ (64 * (h - c - 1)) = Dd := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, isqrt (A * (2 ^ 64 * 2 ^ 64) + P) - s * 2 ^ 64 = q := ⟨_, rfl⟩
  have hAr : s * s + r = A := by omega
  obtain ⟨hN3, hd1, hDβ, ed1, hNu, hUD, hq1, hq2, lo, hi, hqβ, hB, hsq, hrem⟩ :=
    step_arith (β := 2 ^ 64) (H := 2 ^ 63) (show 2 * 2 ^ 63 = 2 ^ 64 from rfl) (show 8 ≤ 2 ^ 64 by omega)
      hPj hK1 hs1 hs2 hr2 hPβ hAr hR hY hN hDd hq
  -- The estimate's words: `N`'s three and `D' = s β / P_k`'s two.
  have hYh : Y / 2 = s * 2 ^ 64 := by
    rw [← hY, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hAh : Ap X (h - 1) = A / (2 ^ (64 * (h - c - 1)) * 2 ^ (64 * (h - c - 1))) := by
    rw [← hA, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add,
      show 64 * (2 * c) + (64 * (h - c - 1) + 64 * (h - c - 1)) = 64 * (2 * (h - 1)) by omega]
  have hv0 : (word t.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / (Dd / 2 ^ 64) - 2 ^ 64 := by
    rw [hI.v, hAh, isqrt_div _ _ hPj, hs, ← ed1]
  refine ⟨WP.mono (stepW_ok hw hwh hI.ct hc1 hch hRw hYw hY0 hy1 hN (by rw [hYh]; exact hDd) hN3 hd1 hDβ hNu hUD
    hq1 hq2 lo hi hqβ hR2 (by rw [pL]; exact hB) hv0) fun t₃ ⟨hzf, ct₃, hz₂, hd₂, FP, k, hw₃⟩ => ⟨hzf, ?_⟩,
    est_ok hw hwh hI.ct hc1 hch hRw hYw hN (by rw [hYh]; exact hDd) hN3 hd1 hDβ hNu hUD hv0⟩
  have hsU : 8 * sU = 208 := rfl
  have hsCt : 8 * sCt = 200 := rfl
  -- The new remainder and root.
  have hA' : Ap X (c - 1) = A * (2 ^ 64 * 2 ^ 64) + P := by
    have dp := div_pair X (c - 1)
    rw [show c - 1 + 1 = c by omega, hP] at dp
    rw [Ap, dp, ← Ap, hA]
  have hz₃ : wv t₃.mem B (slot W sqZ + 8 * (2 * (c - 1))) (h - (c - 1) + 2) = R - (Y + q) * q := by
    rw [show slot W sqZ + 8 * (2 * (c - 1)) = slot W sqZ + 16 * (c - 1) by omega, hz₂]
  have hZ₃ := wv_replace (m := t.mem) (m' := t₃.mem) (d := slot W sqZ) (k := 2 * (c - 1)) (L := h - (c - 1) + 2)
    (N := W) (show 2 * (c - 1) + (h - (c - 1) + 2) ≤ W by omega) hZw hXm hRL
    (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) hz₃
  have hD₀ : wv t.mem B (slot W sqD) W = 0 + 2 ^ (64 * (c - 1)) * Y := by
    rw [hD, pc, ← hY]; grind
  have hD₃ := wv_replace (m := t.mem) (m' := t₃.mem) (d := slot W sqD) (k := c - 1) (L := h - (c - 1) + 2)
    (N := W) (show (c - 1) + (h - (c - 1) + 2) ≤ W by omega) hD₀ hPc hYL
    (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) hd₂
  refine ⟨hw₃, ct₃, ?_, ?_, ?_, hI.frm.trans (FP.mono fun y hy => stepP_sqLP hwh hc1 hch hy),
    (hI.keep.trans k).mono (by decide), ?_⟩
  · rw [hZ₃, hA', hsq, hrem]; exact congrArg _ (Nat.mul_comm _ _)
  · rw [hD₃, hA', hsq, Nat.zero_add, ← hY]; grind
  · rw [FP.word_eq (fun y h1 h2 hy => by omega) (by omega)]; exact hI.v
  · rw [FP.word_eq (fun y h1 h2 hy => by omega) (by omega)]; exact hI.dtop

/-- A digit step at count `c` (`1 ≤ c < h`). -/
theorem stepX_ok {s₀ t : State} {B : Addr} {Z W h X c : Nat} (hwh : W = 2 * h + 4) (hh : h ≤ 128)
    (hX : X < 2 ^ (64 * (2 * h))) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X)
    (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) (hI : SqI s₀ B Z W h X c t) :
    WP isa stepX t fun t' => t'.zf = some (decide (c = 1)) ∧ SqI s₀ B Z W h X (c - 1) t' :=
  (stepXE_ok hwh hh hX hXt hc1 hch hI).1

/-- The digit loop, from count `h - 1` down to `0`. -/
theorem sqLoop_ok {s₀ t : State} {B : Addr} {Z W h X : Nat} (hwh : W = 2 * h + 4) (hh : h ≤ 128)
    (hX : X < 2 ^ (64 * (2 * h))) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X) (h2 : 2 ≤ h)
    (hI : SqI s₀ B Z W h X (h - 1) t) :
    WP isa (.loop stepX .ne) t (SqI s₀ B Z W h X 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ n + 1 ≤ h ∧ SqI s₀ B Z W h X n s) ?_ (h - 1) t
    ⟨by omega, by omega, hI⟩
  rintro n s ⟨h1, h2', hs⟩
  refine WP.mono (stepX_ok hwh hh hX hXt h1 h2' hs) fun s' ⟨hz, hs'⟩ => ?_
  have hev : isa.eval .ne s' = some (!decide (n = 1)) := by simp only [eval, hz, Option.map_some]
  by_cases he : n = 1
  · subst he; exact .inl ⟨by rw [hev]; rfl, hs'⟩
  · exact .inr ⟨by rw [hev, decide_eq_false he]; rfl, n - 1, by omega, by omega, by omega, hs'⟩

end VG.Proof.Rsa.X86_64.Rd
