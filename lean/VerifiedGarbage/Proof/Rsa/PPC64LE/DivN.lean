module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The division of the RSA key operations at the divisor's width, on PPC64LE

`divN_ok`: `divN q r d t` computes what `div q r d t` does (`div_ok`) for a
divisor below `2^(32 wd)`, with `wd` in `r12`, even and at most `w`: the
remainder, the divisor and the temporary are worked on over their `wd + 1`
low digits (`numN`), and the remainder's digits above them stay zero. A step
(`stepN_ok`) is the same `divStep` as `step_ok`'s.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subWBody selWBody evenW)
open VG.Impl.Rsa.PPC64LE.Div (shiftR shiftN subtractN keepN stepN divN divP setWd div init setBit shlBody shlWBody selTop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Proof.Rsa (divStep divIter divIter_inv divIter_done borrow_iff)

/-- The `wd + 1` low digits of array `j`. -/
abbrev numN (m : Mem) (B : Addr) (w wd j : Nat) : Nat := val32 m B (arr w j) (wd + 1)

theorem numN_eq (m : Mem) (B : Addr) (w : Nat) {wd : Nat} (hev : wd % 2 = 0) (j : Nat) :
    numN m B w wd j = wordsVal m B (arr w j) (wd / 2) + 2 ^ (32 * wd) * w32 m B (arr w j + 4 * wd) := by
  rw [numN, val32_succ, wordsVal_eq_val32, show 2 * (wd / 2) = wd by omega_using [hev]]

/-- A number below `2^(32 wd)` with its extra digit 0 is its `wd + 1` low digits. -/
theorem numN_of_lt (m : Mem) (B : Addr) {w wd d : Nat} (hwd : wd ≤ w)
    (hdz : w32 m B (arr w d + 4 * w) = 0) (hlt : num m B w d < 2 ^ (32 * wd)) :
    numN m B w wd d = num m B w d := by
  have e1 : num1 m B w d = num m B w d := by
    rw [num1_eq, hdz, Nat.mul_zero, Nat.add_zero]
  have e2 := val32_append m B (arr w d) (wd + 1) (w - wd)
  rw [show wd + 1 + (w - wd) = w + 1 by omega_using [hwd]] at e2
  change num1 m B w d = _ at e2
  rw [e1] at e2
  have hp : 2 ^ (32 * wd) ≤ 2 ^ (32 * (wd + 1)) := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hz : val32 m B (arr w d + 4 * (wd + 1)) (w - wd) = 0 := by
    by_contra hc
    have : 2 ^ (32 * (wd + 1)) ≤ 2 ^ (32 * (wd + 1)) * val32 m B (arr w d + 4 * (wd + 1)) (w - wd) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc)
    omega_using [hlt, e2, hp, this]
  rw [hz, Nat.mul_zero, Nat.add_zero] at e2
  exact e2.symm

/-- The numbers of a step at the divisor's width: the quotient's `P1` and the
remainder's `PD`. -/
theorem stepN_arith {D R Q Q1 R1 T c c' β P1 PD P2 H : Nat} (hD : 0 < D) (hR : R < D)
    (hDP : D < PD) (hP1 : P1 = 2 * H) (hP2 : P2 = 4294967296 * PD) (hQ1 : Q1 < P1) (hT : T < P2)
    (hc : c ≤ 1) (hβ : β ≤ 1) (e1 : Q1 + P1 * c = 2 * Q) (e2 : R1 + P2 * c' = 2 * R + c)
    (e3 : T + D = R1 + P2 * β) :
    R1 = 2 * R + Q / H ∧ Q1 = 2 * Q % P1 ∧ (β = 0 ↔ D ≤ R1) ∧ (β = 0 → T = R1 - D) := by
  have hH : 0 < H := by omega_arith
  have hc' : c' = 0 := by
    rcases Nat.eq_zero_or_pos c' with z | z
    · exact z
    · have : P2 ≤ P2 * c' := Nat.le_mul_of_pos_right _ z
      omega_arith
  subst hc'
  have hcQ : c = Q / H := by
    have : 2 * Q / P1 = c := by
      rw [← e1, Nat.add_mul_div_left _ _ (by omega_arith), Nat.div_eq_of_lt hQ1, Nat.zero_add]
    rw [← this, hP1, Nat.mul_div_mul_left _ _ (by decide)]
  have hmod : Q1 = 2 * Q % P1 := by
    rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ1]
  have hb := borrow_iff e3 hT hβ
  refine ⟨by omega_arith, hmod, hb, fun h0 => ?_⟩
  rw [h0, Nat.mul_zero, Nat.add_zero] at e3
  omega_arith

/-- `shiftR r`: the remainder's `wd + 1` low digits shifted left, the carry
in `r9` in and out. -/
theorem shiftR_ok {v : State} {B : Addr} {Z w N r wd : Nat} (h : Ws v B Z w N) (hr : r < N) (hN : N ≤ 256)
    (h12 : v.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w)
    (c9 : (v.gpr .r9).toNat ≤ 1) :
    WP isa (shiftR r) v fun t => Ws t B Z w N ∧ Outside B (arr w r) (4 * (wd + 1)) v.mem t.mem ∧
      (∃ c' ≤ 1, numN t.mem B w wd r + 2 ^ (32 * (wd + 1)) * c' = 2 * numN v.mem B w wd r + (v.gpr .r9).toNat) ∧
      Keep opRegs v t := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [shiftR, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) ?_
  refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
      y.gpr .r8 = BitVec.ofNat 64 (wd / 2) ∧ y.gpr .r9 = v.gpr .r9 ∧ y.mem = v.mem)
    (by prun [h12, lsr1_ofNat (show wd < 2 ^ 64 by omega_arith)]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
  have k₀ : Keep opRegs v y := ((Keep.write _ _ _).trans ky).mono (by decide)
  have hy : Ws y B Z w N := h.of_keep k₀
  rw [WP.seq_iff]
  refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith) (by omega_arith))
    fun z ⟨c9', zr, zout, kz, z5⟩ => ?_
  have hz := hy.of_keep kz
  refine WP.mono (shlDigit_ok hz.scr (d := arr w r + 4 * wd) (by rw [z5]; congr 1; omega_arith) c9' (by omega_arith))
    fun t ⟨vd, tm, td, c9'', kt⟩ => ⟨hz.of_keep kt, ?_, ⟨_, c9'', ?_⟩, ?_⟩
  · have zo : Outside B (arr w r) (4 * wd) v.mem z.mem := by
      rw [← ym]; simpa only [show 8 * (wd / 2) = 4 * wd by omega_arith] using zout
    rw [tm]
    intro x hx
    rw [writeW32_outside z.mem B vd (d := arr w r + 4 * wd) (by omega_arith) x (by omega_arith), zo x (by omega_arith)]
  · have zt : w32 z.mem B (arr w r + 4 * wd) = w32 v.mem B (arr w r + 4 * wd) := by
      rw [← ym]; exact zout.w32 (by omega_arith) (by omega_arith)
    have zw : w32 t.mem B (arr w r + 4 * wd) = vd.toNat := by rw [tm, w32_write_self]
    have zv : wordsVal t.mem B (arr w r) (wd / 2) = wordsVal z.mem B (arr w r) (wd / 2) := by
      rw [tm, wordsVal_eq_val32, wordsVal_eq_val32]
      exact (writeW32_outside z.mem B vd (d := arr w r + 4 * wd) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
    rw [zt] at td
    rw [y9, ym] at zr
    rw [numN_eq _ _ _ hev, numN_eq _ _ _ hev, zv, zw, show 2 ^ (32 * (wd + 1)) = 2 ^ (32 * wd) * 2 ^ 32 by
      rw [← Nat.pow_add]; congr 1, show 64 * (wd / 2) = 32 * wd by omega_arith] at *
    generalize 2 ^ (32 * wd) = P at *
    grind
  · exact Keep.mono (rs' := opRegs) ((k₀.trans kz).trans kt) (by decide)

/-- Two distinct arrays, over `wd ≤ w` digits, are each ahead of the other. -/
theorem ahead_of_ne' {w wd o a : Nat} (hwd : wd ≤ w) (h : o ≠ a) : Ahead (arr w o) (arr w a) wd := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega_arith

/-- The `w - wd` digits of array `j` above its `wd + 1` low digits. -/
abbrev highN (m : Mem) (B : Addr) (w wd j : Nat) : Nat := val32 m B (arr w j + 4 * (wd + 1)) (w - wd)

/-- `shiftN q r`: `[q]' + 2^(32 w) c = 2 [q]` and, over the remainder's
`wd + 1` low digits, `[r]' + 2^(32 (wd + 1)) c' = 2 [r] + c`. -/
theorem shiftN_ok {s : State} {B : Addr} {Z w N q r wd : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hN : N ≤ 256) (hqr : q ≠ r)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w) :
    WP isa (shiftN q r) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [q, r] [] s.mem t.mem ∧
      highN t.mem B w wd r = highN s.mem B w wd r ∧
      (∃ c ≤ 1, num t.mem B w q + 2 ^ (32 * w) * c = 2 * num s.mem B w q ∧
        ∃ c' ≤ 1, numN t.mem B w wd r + 2 ^ (32 * (wd + 1)) * c' = 2 * numN s.mem B w wd r + c) ∧
      Keep opRegs s t := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have dqr := arr_disj (w := w) hqr
  rw [shiftN, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w q))) := (Keep.write _ _ _).mono
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r5 = off B (arr w q) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem)
    (by prun; rfl) (by decide)) fun u ⟨⟨u5, u9, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := k₀.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (evenW_ok hu (Q := fun v => Ws v B Z w N ∧ Keep opRegs s v ∧ (v.gpr .r9).toNat ≤ 1 ∧
      Outside B (arr w q) (4 * w) s.mem v.mem ∧
      num v.mem B w q + 2 ^ (32 * w) * (v.gpr .r9).toNat = 2 * num s.mem B w q)
    (fun hev' x mx kx => ?_) (fun hodd x mx kx => ?_)) fun v ⟨hv, kv, c9, vout, vq⟩ => ?_
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt, _⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using tout, ?_⟩
    rw [ym, um, y9, show 64 * (w / 2) = 32 * w by omega_arith] at vq
    rw [num_words _ _ hev', num_words _ _ hev']; simpa using vq
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 w ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        BitVec.add_zero]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; exact tout, ?_⟩
    rw [ym, um, y9] at vq; simpa using vq
  · have v12 : v.gpr .r12 = BitVec.ofNat 64 wd := (kv.gpr _ (by decide)).trans h12
    have rr : numN v.mem B w wd r = numN s.mem B w wd r := vout.val32 (by omega_arith) (by omega_arith)
    have hr' : highN v.mem B w wd r = highN s.mem B w wd r := vout.val32 (by omega_arith) (by omega_arith)
    refine WP.mono (shiftR_ok hv hr hN v12 hev h2 hwd c9) fun t ⟨ht, tout, ⟨c', hc', ec⟩, kt⟩ =>
      ⟨ht, ?_, ?_, ⟨_, c9, ?_, c', hc', ?_⟩, kv.trans' kt⟩
    · exact (KeyWorkspace.Keep.of_arr (o := q) (d := 0) (by simpa using vout) (by omega_arith) (by simp)).trans
        (KeyWorkspace.Keep.of_arr (o := r) (d := 0) (by simpa using tout) (by omega_arith) (by simp))
    · rw [← hr']; exact tout.val32 (by omega_arith) (by omega_arith)
    · rw [show num t.mem B w q = num v.mem B w q from tout.val32 (by omega_arith) (by omega_arith)]; exact vq
    · rw [← rr]; exact ec

/-- `subtractN r d t`: `[t] + [d] = [r] + 2^(32 (wd + 1)) β` over `wd + 1` digits. -/
theorem subtractN_ok {s : State} {B : Addr} {Z w N r d t wd : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256) (htr : t ≠ r) (htd : t ≠ d)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w) :
    WP isa (subtractN r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      numN u.mem B w wd t + numN s.mem B w wd d = numN s.mem B w wd r + 2 ^ (32 * (wd + 1)) * (u.gpr .r9).toNat ∧
      (u.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s u := by
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  have dtr := arr_disj (w := w) htr
  have dtd := arr_disj (w := w) htd
  rw [subtractN]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun u p5 p6 p7 ku mu => ?_
  have hu : Ws u B Z w N := h.of_keep ku
  have u12 : u.gpr .r12 = BitVec.ofNat 64 wd := (ku.gpr _ (by decide)).trans h12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r8] (Q := fun x => x.gpr .r5 = off B (arr w t) ∧ x.gpr .r6 = off B (arr w r) ∧
    x.gpr .r7 = off B (arr w d) ∧ x.gpr .r8 = BitVec.ofNat 64 (wd / 2) ∧
    x.ca = decide (2 ^ 64 ≤ (BitVec.ofNat 64 (wd / 2)).toNat + (2 ^ 64 - 1 - (BitVec.ofNat 64 (wd / 2)).toNat) + 1) ∧
    x.mem = u.mem) ?_ (by decide)) fun v ⟨⟨v5, v6, v7, v8, vc, vm⟩, kv⟩ => ?_
  · mcrun [p5, p6, p7, u12, lsr1_ofNat (show wd < 2 ^ 64 by omega_arith)]
  have vc' : v.ca = true := by
    rw [vc]; exact decide_eq_true (by have := (BitVec.ofNat 64 (wd / 2)).isLt; omega_arith)
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  refine WP.mono (subWLoop_ok hv.scr v5 v6 v7 v8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (aheadW hev (ahead_of_ne' hwd htr)) (aheadW hev (ahead_of_ne' hwd htd))) fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
  have hy := hv.of_keep ky
  refine WP.mono (subDigit_ok hy.scr (dO := arr w t + 4 * wd) (dA := arr w r + 4 * wd) (dB := arr w d + 4 * wd)
    (by rw [y5]; congr 1; omega_arith) (by rw [y6]; congr 1; omega_arith) (by rw [y7]; congr 1; omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun z ⟨vd, zm, zd, b9, kz⟩ => ⟨hy.of_keep kz, ?_, ?_, b9, ?_⟩
  · have yo : Outside B (arr w t + 0) (4 * wd) s.mem y.mem := by
      rw [← mu, ← vm]; simpa only [show 8 * (wd / 2) = 4 * wd by omega_arith, Nat.add_zero] using yout
    rw [zm]
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.of_arr (o := t) yo (by omega_arith) (by simp))
      (KeyWorkspace.Keep.of_arr (o := t) (d := 4 * wd) (writeW32_outside _ _ _ (by omega_arith)) (by omega_arith) (by simp))
  · have hdy : w32 y.mem B (arr w d + 4 * wd) = w32 s.mem B (arr w d + 4 * wd) := by
      rw [← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
    have hry : w32 y.mem B (arr w r + 4 * wd) = w32 s.mem B (arr w r + 4 * wd) := by
      rw [← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
    rw [hdy, hry] at zd
    rw [vc', vm, mu] at veq
    have zv : wordsVal z.mem B (arr w t) (wd / 2) = wordsVal y.mem B (arr w t) (wd / 2) := by
      rw [zm, wordsVal_eq_val32, wordsVal_eq_val32]
      exact (writeW32_outside y.mem B vd (d := arr w t + 4 * wd) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
    rw [numN_eq _ _ _ hev, numN_eq _ _ _ hev, numN_eq _ _ _ hev, zv, zm, w32_write_self,
      show 2 ^ (32 * (wd + 1)) = 2 ^ (32 * wd) * 2 ^ 32 by rw [← Nat.pow_add]; congr 1]
    rw [show 64 * (wd / 2) = 32 * wd by omega_arith] at veq
    simp only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] at veq
    generalize 1 - y.ca.toNat = c at veq zd
    generalize 2 ^ (32 * wd) = P at *
    grind
  · exact Keep.mono (rs' := opRegs) (((ku.trans kv).trans ky).trans kz) (by decide)

/-- `keepN r t`: `[r] := b ? [t] : [r]` over `wd + 1` digits, the mask of `b` in `r9`. -/
theorem keepN_ok {s : State} {B : Addr} {Z w N r t wd : Nat} (h : Ws s B Z w N)
    (hr : r < N) (ht : t < N) (hN : N ≤ 256) (hrt : r ≠ t) {b : Bool}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w) :
    WP isa (keepN r t) s fun u => Ws u B Z w N ∧ Outside B (arr w r) (4 * (wd + 1)) s.mem u.mem ∧
      numN u.mem B w wd r = (if b then numN s.mem B w wd t else numN s.mem B w wd r) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8] s u := by
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  have drt := arr_disj (w := w) hrt
  rw [keepN]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun u p5 p6 p7 ku mu => ?_
  have hu : Ws u B Z w N := h.of_keep ku
  have u9 : u.gpr .r9 = s.gpr .r9 := ku.gpr _ (by decide)
  have u12 : u.gpr .r12 = BitVec.ofNat 64 wd := (ku.gpr _ (by decide)).trans h12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun v => v.gpr .r5 = off B (arr w r) ∧ v.gpr .r6 = off B (arr w r) ∧
    v.gpr .r7 = off B (arr w t) ∧ v.gpr .r8 = BitVec.ofNat 64 (wd / 2) ∧ v.gpr .r9 = s.gpr .r9 ∧ v.mem = u.mem)
    (by prun [p5, p6, p7, u9, u12, lsr1_ofNat (show wd < 2 ^ 64 by omega_arith)])
    (by decide)) fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  refine WP.mono (selWLoop_ok (b := b) hv.scr v5 v6 v7 v8 (by rw [v9, h9]) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _)) (aheadW hev (ahead_of_ne' hwd hrt)))
    fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
  have hy := hv.of_keep ky
  have y9 : y.gpr .r9 = s.gpr .r9 := (ky.gpr _ (by decide)).trans v9
  refine WP.mono (selDigit_ok hy.scr (b := b) (dO := arr w r + 4 * wd) (dA := arr w r + 4 * wd)
    (dB := arr w t + 4 * wd) (by rw [y5]; congr 1; omega_arith) (by rw [y6]; congr 1; omega_arith)
    (by rw [y7]; congr 1; omega_arith) (by rw [y9, h9]) (by omega_arith) (by omega_arith) (by omega_arith))
    fun z ⟨zm, kz⟩ => ⟨hy.of_keep kz, ?_, ?_, ?_⟩
  · have yo : Outside B (arr w r) (4 * wd) s.mem y.mem := by
      rw [← mu, ← vm]; simpa only [show 8 * (wd / 2) = 4 * wd by omega_arith] using yout
    rw [zm]
    intro x hx
    rw [writeW32_outside y.mem B _ (d := arr w r + 4 * wd) (by omega_arith) x (by omega_arith), yo x (by omega_arith)]
  · have hty : w32 y.mem B (arr w t + 4 * wd) = w32 s.mem B (arr w t + 4 * wd) := by
      rw [← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
    have hry : w32 y.mem B (arr w r + 4 * wd) = w32 s.mem B (arr w r + 4 * wd) := by
      rw [← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
    have zv : wordsVal z.mem B (arr w r) (wd / 2) = wordsVal y.mem B (arr w r) (wd / 2) := by
      rw [zm, wordsVal_eq_val32, wordsVal_eq_val32]
      exact (writeW32_outside y.mem B _ (d := arr w r + 4 * wd) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
    rw [vm, mu] at veq
    rw [numN_eq _ _ _ hev, numN_eq _ _ _ hev, numN_eq _ _ _ hev, zv, veq, zm, w32_write_self]
    simp only [w32] at hty hry
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [hry]
    · simp only [ite_true]; rw [hty]
  · exact Keep.mono (((ku.trans kv).trans ky).trans kz) (by decide)

/-- Digits of an array outside the frame. -/
theorem keep_part {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ 160)
    (fit : arr w j + S w ≤ 2 ^ 64) {o n : Nat} (ho : o + 4 * n ≤ S w) :
    val32 m' B (arr w j + o) n = val32 m B (arr w j + o) n := by
  refine Outs.val32 h (fun r hr => ?_) (by omega_arith)
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; simp only [S] at *; omega_arith
  · have := hd d hd'; have : 160 ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- A step at the divisor's width. -/
theorem stepN_ok {s : State} {B : Addr} {Z w N q r d t wd : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w)
    {D N₀ k : Nat} (hk : k < 32 * w) (hN₀ : N₀ < 2 ^ (32 * w)) (hD : numN s.mem B w wd d = D)
    (hDw : D < 2 ^ (32 * wd))
    (vals : 0 < D → num s.mem B w q = (divIter D (32 * w) k (0, N₀)).2 ∧
      numN s.mem B w wd r = (divIter D (32 * w) k (0, N₀)).1) :
    WP isa (stepN q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep stepRegs s u ∧
      highN u.mem B w wd r = highN s.mem B w wd r ∧
      (0 < D → num u.mem B w q = (divIter D (32 * w) (k + 1) (0, N₀)).2 ∧
        numN u.mem B w wd r = (divIter D (32 * w) (k + 1) (0, N₀)).1) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  rw [stepN, WP.seq_iff]
  refine WP.mono (shiftN_ok h hq hr hN hqr h12 hev h2 hwd) fun s1 ⟨h1, km1, hi1, ⟨c, hc, eq1, c', hc', er1⟩, k1⟩ => ?_
  have s12 : s1.gpr .r12 = BitVec.ofNat 64 wd := (k1.gpr _ (by decide)).trans h12
  rw [WP.seq_iff]
  refine WP.mono (subtractN_ok h1 hr hd ht hN (Ne.symm hrt) (Ne.symm hdt) s12 hev h2 hwd)
    fun s2 ⟨h2', km2, eT, hβ, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (bit_ok hβ) fun s3 ⟨⟨r10, r9, m3⟩, k3⟩ => ?_
  have h3 : Ws s3 B Z w N := h2'.of_keep k3
  have t12 : s3.gpr .r12 = BitVec.ofNat 64 wd := (k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans s12)
  rw [WP.seq_iff]
  refine WP.mono (keepN_ok h3 hr ht hN hrt (b := decide ((s2.gpr .r9).toNat = 0))
    (by rw [r9]; by_cases z : (s2.gpr .r9).toNat = 0 <;> simp [z]) t12 hev h2 hwd) fun s4 ⟨h4, o4, eR, k4⟩ => ?_
  have km4 : KeyWorkspace.Keep B w [r] [] s3.mem s4.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (by simpa using o4) (by omega_arith) (by simp)
  have e10 : s4.gpr .r10 = s3.gpr .r10 := k4.gpr _ (by decide)
  have q2 : num s2.mem B w q = num s1.mem B w q :=
    KeyWorkspace.Keep.num km2 (by simp; omega_arith) (by simp) (by omega_arith)
  have q4 : num s4.mem B w q = num s1.mem B w q := by
    rw [KeyWorkspace.Keep.num km4 (by simp; omega_arith) (by simp) (by omega_arith), m3, q2]
  have even : num s4.mem B w q % 2 = 0 := by
    rw [q4]
    have : 2 ∣ 2 ^ (32 * w) * c :=
      Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.pow_mod 2 (32 * w) 2 ▸ by
        rw [Nat.mod_self, Nat.zero_pow (by omega_arith)])) _
    omega_arith
  refine WP.mono (setBit_ok h4 hq hN even (by rw [e10, r10]; split <;> decide))
    fun u ⟨hu, km5, eQ, u4, k5⟩ => ?_
  have kr : Keep stepRegs s u := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  have k12 : KeyWorkspace.Keep B w [q, r, t] [] s.mem s2.mem := KeyWorkspace.Keep.join km1 km2
  have k45 : KeyWorkspace.Keep B w [q, r, t] [] s2.mem u.mem := by
    rw [← m3]; exact KeyWorkspace.Keep.join km4 km5
  have hi : highN u.mem B w wd r = highN s.mem B w wd r := by
    rw [← hi1]
    have a2 : highN s2.mem B w wd r = highN s1.mem B w wd r :=
      keep_part km2 (by simp; omega_arith) (by simp) (by omega_arith) (by simp only [S]; omega_arith)
    have a4 : highN s4.mem B w wd r = highN s3.mem B w wd r := o4.val32 (by omega_arith) (by omega_arith)
    have a5 : highN u.mem B w wd r = highN s4.mem B w wd r :=
      keep_part km5 (by simp; omega_arith) (by simp) (by omega_arith) (by simp only [S]; omega_arith)
    rw [a5, a4, m3, a2]
  refine ⟨hu, k12.trans k45, ?_, kr, hi, fun hD0 => ?_⟩
  · rw [u4, k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  · obtain ⟨vq, vr⟩ := vals hD0
    obtain ⟨_, hR, -, -, -⟩ := divIter_inv hD0 hN₀ k (by omega_arith)
    have es : divIter D (32 * w) (k + 1) (0, N₀) = divStep D (32 * w) (divIter D (32 * w) k (0, N₀)) := rfl
    have d1 : numN s1.mem B w wd d = D := by
      have e := keep_part km1 (j := d) (by simp; omega_arith) (by simp) (by omega_arith) (o := 0) (n := wd + 1)
        (by simp only [S]; omega_arith)
      simp only [Nat.add_zero] at e
      rw [← hD]; exact e
    have r2 : numN s2.mem B w wd r = numN s1.mem B w wd r := by
      have e := keep_part km2 (j := r) (by simp; omega_arith) (by simp) (by omega_arith) (o := 0) (n := wd + 1)
        (by simp only [S]; omega_arith)
      simp only [Nat.add_zero] at e
      exact e
    have t3 : numN s3.mem B w wd t = numN s2.mem B w wd t := by rw [m3]
    have ur : numN u.mem B w wd r = numN s4.mem B w wd r := by
      have e := keep_part km5 (j := r) (by simp; omega_arith) (by simp) (by omega_arith) (o := 0) (n := wd + 1)
        (by simp only [S]; omega_arith)
      simp only [Nat.add_zero] at e
      exact e
    have hP2 : 2 ^ (32 * (wd + 1)) = 4294967296 * 2 ^ (32 * wd) := by
      rw [show 32 * (wd + 1) = 32 + 32 * wd by omega_arith, Nat.pow_add]
    have hP1 : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, 32 * w = j + 1 := ⟨32 * w - 1, by omega_arith⟩
      rw [hj, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hQ1 : num s1.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
    have hT : numN s2.mem B w wd t < 2 ^ (32 * (wd + 1)) := val32_lt _ _ _ _
    rw [d1] at eT
    have hR' : numN s.mem B w wd r < D := by rw [vr]; exact hR
    obtain ⟨eR1, eQ1, hb, hTv⟩ := stepN_arith hD0 hR' hDw hP1 hP2 hQ1 hT hc hβ eq1 er1 eT
    have ep : divIter D (32 * w) k (0, N₀) = (numN s.mem B w wd r, num s.mem B w q) :=
      Prod.ext vr.symm vq.symm
    rw [es, ep]
    simp only [divStep]
    rw [ur, eR, t3, m3, r2, eQ, e10, r10, q4, ← eR1, ← eQ1]
    by_cases hl : numN s1.mem B w wd r < D
    · have hβ1 : (s2.gpr .r9).toNat ≠ 0 := fun z => absurd (hb.mp z) (by omega_arith)
      simp only [hl, hβ1, ↓reduceIte, decide_false]
      exact ⟨by simp, rfl⟩
    · have hβ0 : (s2.gpr .r9).toNat = 0 := hb.mpr (by omega_arith)
      simp only [hl, hβ0, ↓reduceIte, decide_true]
      exact ⟨by simp, hTv hβ0⟩

/-- `divN q r d t`: `div_ok`'s results for a divisor below `2^(32 wd)`. -/
theorem divN_ok {s : State} {B : Addr} {Z w N q r d t wd : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hdz : w32 s.mem B (arr w d + 4 * w) = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wd) (hev : wd % 2 = 0) (h2 : 2 ≤ wd) (hwd : wd ≤ w)
    (hlt : num s.mem B w d < 2 ^ (32 * wd)) :
    WP isa (divN q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      Keep stepRegs s u ∧
      (0 < num s.mem B w d → num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d) := by
  have fd := h.arr_fit hd
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have hD : numN s.mem B w wd d = num s.mem B w d := numN_of_lt _ _ hwd hdz hlt
  have hN₀ : num s.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
  have split : ∀ m : Mem, num1 m B w r = numN m B w wd r + 2 ^ (32 * (wd + 1)) * highN m B w wd r := by
    intro m
    have e := val32_append m B (arr w r) (wd + 1) (w - wd)
    rwa [show wd + 1 + (w - wd) = w + 1 by omega_arith] at e
  rw [divN, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u4, ku⟩ => ?_
  have zs := split u.mem
  rw [z] at zs
  have z1 : numN u.mem B w wd r = 0 := by omega_arith
  have z2 : highN u.mem B w wd r = 0 := by
    rcases Nat.eq_zero_or_pos (highN u.mem B w wd r) with e | e
    · exact e
    · have : 2 ^ (32 * (wd + 1)) ≤ 2 ^ (32 * (wd + 1)) * highN u.mem B w wd r := Nat.le_mul_of_pos_right _ e
      have := Nat.two_pow_pos (32 * (wd + 1))
      omega_arith
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem x.mem ∧ Keep stepRegs s x ∧
      highN x.mem B w wd r = 0 ∧
      (0 < D → num x.mem B w q = (divIter D (32 * w) i (0, N₀)).2 ∧
        numN x.mem B w wd r = (divIter D (32 * w) i (0, N₀)).1)
  have i0 : Inv 0 u := ⟨hu, km.mono, ku.mono, z2, fun _ => ⟨KeyWorkspace.Keep.num km (by simp; omega_arith)
    (by simp) (by have := h.fit64 hq; omega_arith), z1⟩⟩
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := stepN q r d t) (cnt := .r4) (N := 32 * w)
    (by omega_arith) (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, zx, vx⟩ _ => ?_) i0 u4)
    fun x ⟨hx, kx, rx, zx, vx⟩ => ?_
  · have dx : numN x.mem B w wd d = D := by
      have e := keep_part kx (j := d) (by simp; omega_arith) (by simp) (by omega_arith) (o := 0) (n := wd + 1)
        (by simp only [S]; omega_arith)
      simp only [Nat.add_zero] at e
      exact e.trans hD
    have x12 : x.gpr .r12 = BitVec.ofNat 64 wd := (rx.gpr _ (by decide)).trans h12
    refine WP.mono (stepN_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt x12 hev h2 hwd hi hN₀ dx hlt vx)
      fun y ⟨hy, ky, y4, ry, zy, vy⟩ => ⟨⟨hy, kx.trans ky, rx.trans' ry, by rw [zy]; exact zx, vy⟩, y4⟩
  · refine ⟨hx, kx, rx, fun hD0 => ?_⟩
    obtain ⟨e1, e2⟩ := vx hD0
    rw [divIter_done hD0 hN₀] at e1 e2
    refine ⟨e1, ?_⟩
    rw [split, zx, Nat.mul_zero, Nat.add_zero]
    exact e2

theorem setWd_r12 {L : Nat} (hL : L < 2 ^ 32) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (2 * ((L + 7) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_arith

theorem setWd_r0 {w wd : Nat} (hw : w < 2 ^ 32) (hwd : wd < 2 ^ 32) :
    (BitVec.ofNat 64 w - BitVec.ofNat 64 wd) >>> 63 = BitVec.ofNat 64 (decide (w < wd)).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  by_cases h : w < wd <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `divP q r d t`: `div_ok`'s results, for a divisor of `L ≥ 1` bytes
(`L` in `r12`). -/
theorem divP_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hdz : w32 s.mem B (arr w d + 4 * w) = 0) {L : Nat}
    (hlen : s.gpr .r12 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 32)
    (hlt : num s.mem B w d < 2 ^ (8 * L)) :
    WP isa (divP q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      Keep (.r12 :: stepRegs) s u ∧
      (0 < num s.mem B w d → num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d) := by
  have := h.wle
  have := h.wpos
  rw [divP, WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun x => x.gpr .r12 = BitVec.ofNat 64 (2 * ((L + 7) / 8)) ∧
      x.gpr .r0 = BitVec.ofNat 64 (decide (w < 2 * ((L + 7) / 8))).toNat ∧ x.mem = s.mem)
    (by prun [setWd, hlen, h.r29, setWd_r12 hL,
      setWd_r0 (show w < 2 ^ 32 by omega_arith) (show 2 * ((L + 7) / 8) < 2 ^ 32 by omega_arith)])
    (by decide)) fun x ⟨⟨x12, x0, xm⟩, kx⟩ => ?_
  have hx : Ws x B Z w N := h.of_keep kx
  have xdz : w32 x.mem B (arr w d + 4 * w) = 0 := by rw [xm]; exact hdz
  have xd : num x.mem B w d = num s.mem B w d := by rw [xm]
  have xq : num x.mem B w q = num s.mem B w q := by rw [xm]
  refine WP.ite _ (VG.PPC64LE.eval_zero_ofNat x .r0 (k := (decide (w < 2 * ((L + 7) / 8))).toNat)
    (by cases decide (w < 2 * ((L + 7) / 8)) <;> decide) x0) (fun e => ?_) (fun e => ?_)
  · have hwd : 2 * ((L + 7) / 8) ≤ w := by
      by_contra hc
      rw [decide_eq_true (show w < 2 * ((L + 7) / 8) by omega_arith)] at e
      simp at e
    have hp : 2 ^ (8 * L) ≤ 2 ^ (32 * (2 * ((L + 7) / 8))) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    refine WP.mono (divN_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt xdz x12 (by omega_arith) (by omega_arith) hwd
      (by rw [xd]; omega_arith)) fun u ⟨hu, ku, ru, vu⟩ => ⟨hu, by rw [← xm]; exact ku, ?_, ?_⟩
    · exact (kx.trans ru).mono (by decide)
    · rw [← xd, ← xq]; exact vu
  · refine WP.mono (div_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt xdz) fun u ⟨hu, ku, ru, vu⟩ =>
      ⟨hu, by rw [← xm]; exact ku, ?_, ?_⟩
    · exact (kx.trans ru).mono (by decide)
    · rw [← xd, ← xq]; exact vu

end VG.Proof.Rsa.PPC64LE.Keys
