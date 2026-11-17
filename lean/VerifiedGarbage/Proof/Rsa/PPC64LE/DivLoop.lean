module

public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps

/-! ### `Rsa.PPC64LE.Div`, which this module and modules that import it used -/

section

/-!
# The division of the RSA key operations on PPC64LE: the parts of a step

`shift_ok`: the quotient (`w` digits) and the remainder (`w + 1`) shifted
left together, the quotient's top bit into the remainder; `subtract_ok`:
`[t] := [r] - [d]` over `w + 1` digits; `keep_ok`: `[r] := mask ? [t] : [r]`;
`setBit_ok`: the new bit into the quotient's low digit. For an even `w` the
loops run over `w / 2` words, the remainder's top digit on its own after
them (`shlDigit_ok`, `subDigit_ok`, `selDigit_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subBody selBody subWBody selWBody)
open VG.Impl.Rsa.PPC64LE.Div (shift subtract keep setBit shlBody shlWBody selTop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)

/-- The `w + 1` digits of array `j`. -/
abbrev num1 (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (arr w j) (w + 1)

/-- A digit of the left shift on its own (`shlBody`). -/
theorem shlDigit_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B d)
    (h9 : (s.gpr .r9).toNat ≤ 1) (hd : d + 4 ≤ Z) :
    WP isa (.block shlBody) s fun t => ∃ v : BitVec 32, t.mem = s.mem.writeW (off B d) v ∧
      v.toNat + 2 ^ 32 * (t.gpr .r9).toNat = 2 * w32 s.mem B d + (s.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep loopRegs s t := by
  refine WP.mono (WP.keep loopRegs (Q := fun t => t.gpr .r9 = (s.mem.readW (off B d) 32).setWidth 64 >>> 31 ∧
    t.mem = s.mem.writeW (off B d) ((((s.mem.readW (off B d) 32).setWidth 64 <<< 1) ||| s.gpr .r9).setWidth 32))
    ?_ (by decide)) fun t ⟨⟨t9, tm⟩, kt⟩ => ⟨_, tm, ?_, ?_, kt⟩
  · prun [shlBody, h5, hs.ld (show d + 4 ≤ Z by omega_arith), hs.st (show d + 4 ≤ Z by omega_arith)]
  · rw [t9]; exact (shl_arith _ _ h9).1
  · rw [t9]; exact (shl_arith _ _ h9).2

/-- The top digit of the subtraction with the carry bit (`sube`): its borrow
in the sign bit of the 64-bit difference. -/
theorem subD_arith (a b : BitVec 32) (c : Bool) :
    ((BitVec.ofNat 64 (a.toNat + (2 ^ 64 - 1 - b.toNat) + c.toNat)).setWidth 32).toNat + b.toNat + (1 - c.toNat) =
        a.toNat + 2 ^ 32 * (BitVec.ofNat 64 (a.toNat + (2 ^ 64 - 1 - b.toNat) + c.toNat) >>> 63).toNat ∧
      (BitVec.ofNat 64 (a.toNat + (2 ^ 64 - 1 - b.toNat) + c.toNat) >>> 63).toNat ≤ 1 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> constructor <;> omega_arith

/-- The top digit of the subtraction on its own, the borrow in the carry bit
in and in `r9` out. -/
theorem subDigit_ok {s : State} {B : Addr} {Z dO dA dB : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B dO)
    (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB) (hO : dO + 4 ≤ Z) (hA : dA + 4 ≤ Z)
    (hB : dB + 4 ≤ Z) :
    WP isa (.block [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .sube .r0 .r0 .r3, .store .w .r0 .r5 0,
        .lsr .d .r9 .r0 63]) s fun t => ∃ v : BitVec 32, t.mem = s.mem.writeW (off B dO) v ∧
      v.toNat + w32 s.mem B dB + (1 - s.ca.toNat) = w32 s.mem B dA + 2 ^ 32 * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep loopRegs s t := by
  refine WP.mono (WP.keep loopRegs (Q := fun t =>
    t.gpr .r9 = BitVec.ofNat 64 ((s.mem.readW (off B dA) 32).toNat +
      (2 ^ 64 - 1 - (s.mem.readW (off B dB) 32).toNat) + s.ca.toNat) >>> 63 ∧
    t.mem = s.mem.writeW (off B dO) ((BitVec.ofNat 64 ((s.mem.readW (off B dA) 32).toNat +
      (2 ^ 64 - 1 - (s.mem.readW (off B dB) 32).toNat) + s.ca.toNat)).setWidth 32))
    ?_ (by decide)) fun t ⟨⟨t9, tm⟩, kt⟩ => ⟨_, tm, ?_, ?_, kt⟩
  · mcrun [h5, h6, h7, hs.ld (show dA + 4 ≤ Z by omega_arith), hs.ld (show dB + 4 ≤ Z by omega_arith),
      hs.st (show dO + 4 ≤ Z by omega_arith), toNat_ext32]
  · rw [t9]; exact (subD_arith _ _ _).1
  · rw [t9]; exact (subD_arith _ _ _).2

/-- A digit of the selection on its own. -/
theorem selDigit_ok {s : State} {B : Addr} {Z dO dA dB : Nat} (hs : Scr s B Z) {b : Bool}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hO : dO + 4 ≤ Z) (hA : dA + 4 ≤ Z) (hB : dB + 4 ≤ Z) :
    WP isa (.block selTop) s fun t =>
      t.mem = s.mem.writeW (off B dO) (if b then s.mem.readW (off B dB) 32 else s.mem.readW (off B dA) 32) ∧
      Keep selRegs s t := by
  refine WP.keep _ ?_ (by decide)
  prun [selTop, h5, h6, h7, h9, hs.ld (show dA + 4 ≤ Z by omega_arith), hs.ld (show dB + 4 ≤ Z by omega_arith),
    hs.st (show dO + 4 ≤ Z by omega_arith), select_arith]

/-- `w` digits and one more. -/
theorem num1_eq (m : Mem) (B : Addr) (w j : Nat) :
    num1 m B w j = num m B w j + 2 ^ (32 * w) * w32 m B (arr w j + 4 * w) := val32_succ _ _ _ _

/-- `shift q r`: `[q]' + 2^(32 w) c = 2 [q]` and `[r]' + 2^(32 (w + 1)) c' = 2 [r] + c`, `[r]` of
`w + 1` digits. -/
theorem shift_ok {s : State} {B : Addr} {Z w N q r : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hN : N ≤ 256) (hqr : q ≠ r) :
    WP isa (shift q r) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [q, r] [] s.mem t.mem ∧
      (∃ c ≤ 1, num t.mem B w q + 2 ^ (32 * w) * c = 2 * num s.mem B w q ∧
        ∃ c' ≤ 1, num1 t.mem B w r + 2 ^ (32 * (w + 1)) * c' = 2 * num1 s.mem B w r + c) ∧
      Keep opRegs s t := by
  obtain fq := h.arr_fit hq
  obtain fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  obtain dqr := arr_disj (w := w) hqr
  rw [shift, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  obtain k₀ : Keep opRegs s (s.write .r5 (off B (arr w q))) := (Keep.write _ _ _).mono
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r5 = off B (arr w q) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem)
    (by prun; rfl) (by decide)) fun u ⟨⟨u5, u9, um⟩, ku⟩ => ?_
  obtain k₁ : Keep opRegs s u := k₀.trans' ku.mono
  obtain hu : Ws u B Z w N := h.of_keep k₁
  -- The quotient: `[q]' + 2^(32 w) c = 2 [q]`, and the rest after it.
  obtain rest : ∀ v : State, Ws v B Z w N → Keep opRegs s v → (v.gpr .r9).toNat ≤ 1 →
      Outside B (arr w q) (4 * w) s.mem v.mem →
      num v.mem B w q + 2 ^ (32 * w) * (v.gpr .r9).toNat = 2 * num s.mem B w q →
      WP isa (.seq (.block (ptr .r5 r)) (VG.Impl.Rsa.PPC64LE.Keys.evenW
          (.seq (.block [.lsr .d .r8 .r29 1]) (.seq (countLoop .r8 shlWBody) (.block shlBody)))
          (.seq (.block [.addi .r8 .r29 1]) (countLoop .r8 shlBody)))) v fun t =>
        Ws t B Z w N ∧ KeyWorkspace.Keep B w [q, r] [] s.mem t.mem ∧
        (∃ c ≤ 1, num t.mem B w q + 2 ^ (32 * w) * c = 2 * num s.mem B w q ∧
          ∃ c' ≤ 1, num1 t.mem B w r + 2 ^ (32 * (w + 1)) * c' = 2 * num1 s.mem B w r + c) ∧
        Keep opRegs s t := by
    intro v hv kv c9 vout vq
    obtain k₁v : KeyWorkspace.Keep B w [q, r] [] s.mem v.mem :=
      KeyWorkspace.Keep.of_arr (d := 0) (by simpa using vout) (by omega_arith) (by simp)
    obtain rr : num1 v.mem B w r = num1 s.mem B w r := vout.val32 (by omega_arith) (by omega_arith)
    rw [WP.seq_iff, ← List.append_nil (ptr .r5 r)]
    refine ptr_ok hv (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
    obtain hx0 : Ws (v.write .r5 (off B (arr w r))) B Z w N := hv.of_keep (Keep.write _ _ _)
    have x9 : (v.write .r5 (off B (arr w r))).gpr .r9 = v.gpr .r9 := rfl
    refine evenW_ok hx0 (fun hev x mx kx => ?_) (fun hodd x mx kx => ?_)
    · have x5 : x.gpr .r5 = off B (arr w r) := by rw [kx.gpr _ (by decide)]; rfl
      obtain hx := hx0.of_keep kx
      rw [WP.seq_iff]
      refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
        y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = v.gpr .r9 ∧ y.mem = v.mem)
        (by prun [x5, hx.r29, kx.gpr (r := .r9) (by decide), x9, mx, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)])
        (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
      obtain hy := hx.of_keep ky
      rw [WP.seq_iff]
      refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith) (by omega_arith))
        fun z ⟨c9', zr, zout, kz, z5⟩ => ?_
      obtain hz := hy.of_keep kz
      refine WP.mono (shlDigit_ok hz.scr (d := arr w r + 4 * w) (by rw [z5]; congr 1; omega_arith) c9' (by omega_arith))
        fun t ⟨vd, tm, td, c9'', kt⟩ => ⟨hz.of_keep kt, ?_, ⟨_, c9, ?_, _, c9'', ?_⟩, ?_⟩
      · have zo : Outside B (arr w r + 0) (4 * w) v.mem z.mem := by
          rw [← ym]; simpa only [show 8 * (w / 2) = 4 * w by omega_arith, Nat.add_zero] using zout
        rw [tm]
        exact k₁v.trans (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.of_arr (o := r) zo (by omega_arith) (by simp))
          (KeyWorkspace.Keep.of_arr (o := r) (d := 4 * w) (writeW32_outside _ _ _ (by omega_arith)) (by omega_arith) (by simp)))
      · rw [tm, show num (z.mem.writeW (off B (arr w r + 4 * w)) vd) B w q = num v.mem B w q from ?_]
        · exact vq
        · rw [show num v.mem B w q = num z.mem B w q from ?_]
          · exact (writeW32_outside _ _ _ (by omega_arith)).val32 (by omega_arith) (by omega_arith)
          · rw [← ym]; exact (zout.val32 (by omega_arith) (by omega_arith)).symm
      · have zt : w32 z.mem B (arr w r + 4 * w) = w32 v.mem B (arr w r + 4 * w) := by
          rw [← ym]; exact zout.w32 (by omega_arith) (by omega_arith)
        obtain zn : num t.mem B w r = num z.mem B w r := by
          rw [tm]; exact (writeW32_outside z.mem B vd (d := arr w r + 4 * w) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
        obtain zw : w32 t.mem B (arr w r + 4 * w) = vd.toNat := by rw [tm, w32_write_self]
        rw [zt] at td
        rw [y9, ym, show 64 * (w / 2) = 32 * w by omega_arith, ← num_words _ _ hev, ← num_words _ _ hev] at zr
        rw [← rr, num1_eq, num1_eq, zn, zw, show 2 ^ (32 * (w + 1)) = 2 ^ (32 * w) * 2 ^ 32 by
          rw [← Nat.pow_add]; congr 1]
        generalize 2 ^ (32 * w) = P at *
        grind
      · exact Keep.mono (rs' := opRegs) (((((kv.trans (Keep.write _ _ _)).trans kx).trans ky).trans kz).trans kt)
          (by decide)
    · have x5 : x.gpr .r5 = off B (arr w r) := by rw [kx.gpr _ (by decide)]; rfl
      obtain hx := hx0.of_keep kx
      rw [WP.seq_iff]
      refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
        y.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ y.gpr .r9 = v.gpr .r9 ∧ y.mem = v.mem)
        (by prun [x5, hx.r29, kx.gpr (r := .r9) (by decide), x9, mx, BitVec.ofNat_add])
        (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
      obtain hy := hx.of_keep ky
      refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith) (by omega_arith))
        fun t ⟨c9', vr, tout, kt⟩ => ⟨hy.of_keep kt, ?_, ⟨_, c9, ?_, _, c9', ?_⟩, ?_⟩
      · have to : Outside B (arr w r + 0) (4 * (w + 1)) v.mem t.mem := by rw [← ym]; simpa using tout
        exact k₁v.trans (KeyWorkspace.Keep.of_arr (o := r) to (by omega_arith) (by simp))
      · rw [show num t.mem B w q = num v.mem B w q by rw [← ym]; exact tout.val32 (by omega_arith) (by omega_arith)]
        exact vq
      · rw [ym, y9] at vr; rw [← rr]; exact vr
      · exact Keep.mono (rs' := opRegs) ((((kv.trans (Keep.write _ _ _)).trans kx).trans ky).trans kt) (by decide)
  rw [WP.seq_iff]
  refine WP.mono (evenW_ok hu (Q := fun v => Ws v B Z w N ∧ Keep opRegs s v ∧ (v.gpr .r9).toNat ≤ 1 ∧
      Outside B (arr w q) (4 * w) s.mem v.mem ∧
      num v.mem B w q + 2 ^ (32 * w) * (v.gpr .r9).toNat = 2 * num s.mem B w q)
    (fun hev x mx kx => ?_) (fun hodd x mx kx => ?_)) fun v ⟨hv, kv, c9, vout, vq⟩ => rest v hv kv c9 vout vq
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    obtain hy := hx.of_keep ky
    refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt, _⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using tout, ?_⟩
    rw [ym, um, y9, show 64 * (w / 2) = 32 * w by omega_arith] at vq
    rw [num_words _ _ hev, num_words _ _ hev]; simpa using vq
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 w ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        BitVec.add_zero]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    obtain hy := hx.of_keep ky
    refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; exact tout, ?_⟩
    rw [ym, um, y9] at vq; simpa using vq

/-- Two distinct arrays, over `w + 1` digits, are each ahead of the other. -/
theorem ahead1_of_ne {w o a : Nat} (h : o ≠ a) : Ahead (arr w o) (arr w a) (w + 1) := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega_arith

/-- `subtract r d t`: `[t] + [d] = [r] + 2^(32 (w + 1)) β`, over `w + 1` digits. -/
theorem subtract_ok {s : State} {B : Addr} {Z w N r d t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256) (htr : t ≠ r) (htd : t ≠ d) :
    WP isa (subtract r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      num1 u.mem B w t + num1 s.mem B w d = num1 s.mem B w r + 2 ^ (32 * (w + 1)) * (u.gpr .r9).toNat ∧
      (u.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s u := by
  obtain fr := h.arr_fit hr
  obtain fd := h.arr_fit hd
  obtain ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  obtain dtr := arr_disj (w := w) htr
  obtain dtd := arr_disj (w := w) htd
  rw [subtract]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  obtain hx0 : Ws x B Z w N := h.of_keep kx
  refine evenW_ok hx0 (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := hx0.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun x => x.gpr .r5 = off B (arr w t) ∧ x.gpr .r6 = off B (arr w r) ∧
      x.gpr .r7 = off B (arr w d) ∧ x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧
      x.ca = decide (2 ^ 64 ≤ (BitVec.ofNat 64 (w / 2)).toNat + (2 ^ 64 - 1 - (BitVec.ofNat 64 (w / 2)).toNat) + 1) ∧
      x.mem = u.mem) ?_ (by decide)) fun v ⟨⟨v5, v6, v7, v8, vc, vm⟩, kv⟩ => ?_
    · mcrun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide), p5, p6,
        p7, hu.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]
    obtain vc' : v.ca = true := by
      rw [vc]; exact decide_eq_true (by have := (BitVec.ofNat 64 (w / 2)).isLt; omega_arith)
    obtain hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (subWLoop_ok hv.scr v5 v6 v7 v8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (aheadW hev (ahead_of_ne htr)) (aheadW hev (ahead_of_ne htd))) fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
    obtain hy := hv.of_keep ky
    refine WP.mono (subDigit_ok hy.scr (dO := arr w t + 4 * w) (dA := arr w r + 4 * w) (dB := arr w d + 4 * w)
      (by rw [y5]; congr 1; omega_arith) (by rw [y6]; congr 1; omega_arith) (by rw [y7]; congr 1; omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun z ⟨vd, zm, zd, b9, kz⟩ => ⟨hy.of_keep kz, ?_, ?_, b9, ?_⟩
    · have yo : Outside B (arr w t + 0) (4 * w) s.mem y.mem := by
        rw [← mx, ← mu, ← vm]; simpa only [show 8 * (w / 2) = 4 * w by omega_arith, Nat.add_zero] using yout
      rw [zm]
      exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.of_arr (o := t) yo (by omega_arith) (by simp))
        (KeyWorkspace.Keep.of_arr (o := t) (d := 4 * w) (writeW32_outside _ _ _ (by omega_arith)) (by omega_arith) (by simp))
    · have hdy : w32 y.mem B (arr w d + 4 * w) = w32 s.mem B (arr w d + 4 * w) := by
        rw [← mx, ← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
      obtain hry : w32 y.mem B (arr w r + 4 * w) = w32 s.mem B (arr w r + 4 * w) := by
        rw [← mx, ← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
      rw [hdy, hry] at zd
      rw [vc', vm, mu, mx, ← num_words _ _ hev, ← num_words _ _ hev, ← num_words _ _ hev,
        show 64 * (w / 2) = 32 * w by omega_arith] at veq
      rw [num1_eq, num1_eq, num1_eq, zm, w32_write_self,
        show num (y.mem.writeW (off B (arr w t + 4 * w)) vd) B w t = num y.mem B w t from
          (writeW32_outside _ _ _ (by omega_arith)).val32 (by omega_arith) (by omega_arith),
        show 2 ^ (32 * (w + 1)) = 2 ^ (32 * w) * 2 ^ 32 by rw [← Nat.pow_add]; congr 1]
      simp only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] at veq
      generalize 1 - y.ca.toNat = c at veq zd
      generalize 2 ^ (32 * w) = P at *
      grind
    · exact Keep.mono (rs' := opRegs) ((((kx.trans ku).trans kv).trans ky).trans kz) (by decide)
  · have hb : WP isa (.block [.addi .r8 .r29 1, .li .r9 0]) u fun v =>
        (v.gpr .r5 = off B (arr w t) ∧ v.gpr .r6 = off B (arr w r) ∧ v.gpr .r7 = off B (arr w d) ∧
          v.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ v.gpr .r9 = 0 ∧ v.mem = u.mem) ∧ Keep [.r8, .r9] u v := by
      refine WP.keep _ ?_ (by decide)
      prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide), p5, p6,
        p7, (hx0.of_keep ku).r29, BitVec.ofNat_add]
      rfl
    rw [WP.seq_iff]
    refine WP.mono hb fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
    obtain k₁ : Keep opRegs s v := ((kx.trans ku).trans kv).mono (by decide)
    obtain hv : Ws v B Z w N := h.of_keep k₁
    refine WP.mono (subLoop_ok hv.scr v5 v6 v7 v8 (by rw [v9]; decide) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (ahead1_of_ne htr) (ahead1_of_ne htd)) ?_
    intro y ⟨b9, vv, out, ky⟩
    rw [v9, vm, mu, mx] at vv
    rw [vm, mu, mx] at out
    exact ⟨hv.of_keep ky, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
      (by omega_arith) (by simp), by simpa using vv, b9, k₁.trans' ky⟩

/-- `keep r t`: `[r] := b ? [t] : [r]` over `w + 1` digits, the mask of `b` in `r9`. -/
theorem keep_ok {s : State} {B : Addr} {Z w N r t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (ht : t < N) (hN : N ≤ 256) (hrt : r ≠ t) {b : Bool}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (keep r t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = (if b then num1 s.mem B w t else num1 s.mem B w r) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8] s u := by
  obtain fr := h.arr_fit hr
  obtain ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  obtain drt := arr_disj (w := w) hrt
  rw [keep]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  obtain hx0 : Ws x B Z w N := h.of_keep kx
  obtain x9 : x.gpr .r9 = s.gpr .r9 := kx.gpr _ (by decide)
  refine evenW_ok hx0 (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := hx0.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun v => v.gpr .r5 = off B (arr w r) ∧ v.gpr .r6 = off B (arr w r) ∧
      v.gpr .r7 = off B (arr w t) ∧ v.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ v.gpr .r9 = s.gpr .r9 ∧ v.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide),
        ku.gpr (r := .r9) (by decide), p5, p6, p7, x9, hu.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)])
      (by decide)) fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
    obtain hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (selWLoop_ok (b := b) hv.scr v5 v6 v7 v8 (by rw [v9, h9]) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (.inl (Nat.le_refl _)) (aheadW hev (ahead_of_ne hrt))) fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
    obtain hy := hv.of_keep ky
    obtain y9 : y.gpr .r9 = s.gpr .r9 := (ky.gpr _ (by decide)).trans v9
    refine WP.mono (selDigit_ok hy.scr (b := b) (dO := arr w r + 4 * w) (dA := arr w r + 4 * w)
      (dB := arr w t + 4 * w) (by rw [y5]; congr 1; omega_arith) (by rw [y6]; congr 1; omega_arith)
      (by rw [y7]; congr 1; omega_arith) (by rw [y9, h9]) (by omega_arith) (by omega_arith) (by omega_arith))
      fun z ⟨zm, kz⟩ => ⟨hy.of_keep kz, ?_, ?_, ?_⟩
    · have yo : Outside B (arr w r + 0) (4 * w) s.mem y.mem := by
        rw [← mx, ← mu, ← vm]; simpa only [show 8 * (w / 2) = 4 * w by omega_arith, Nat.add_zero] using yout
      rw [zm]
      exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.of_arr (o := r) yo (by omega_arith) (by simp))
        (KeyWorkspace.Keep.of_arr (o := r) (d := 4 * w) (writeW32_outside _ _ _ (by omega_arith)) (by omega_arith) (by simp))
    · have hty : w32 y.mem B (arr w t + 4 * w) = w32 s.mem B (arr w t + 4 * w) := by
        rw [← mx, ← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
      obtain hry : w32 y.mem B (arr w r + 4 * w) = w32 s.mem B (arr w r + 4 * w) := by
        rw [← mx, ← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
      obtain veq' : num y.mem B w r = if b then num s.mem B w t else num s.mem B w r := by
        rw [num_words _ _ hev, num_words _ _ hev, num_words _ _ hev, veq, vm, mu, mx]
      rw [num1_eq, num1_eq, num1_eq, zm, w32_write_self,
        show num (y.mem.writeW (off B (arr w r + 4 * w)) _) B w r = num y.mem B w r from
          (writeW32_outside _ _ _ (by omega_arith)).val32 (by omega_arith) (by omega_arith), veq']
      simp only [w32] at hty hry
      cases b
      · simp only [Bool.false_eq_true, ite_false]; rw [hry]
      · simp only [ite_true]; rw [hty]
    · exact Keep.mono ((((kx.trans ku).trans kv).trans ky).trans kz) (by decide)
  · have hb : WP isa (.block [.addi .r8 .r29 1]) u fun v =>
        (v.gpr .r5 = off B (arr w r) ∧ v.gpr .r6 = off B (arr w r) ∧ v.gpr .r7 = off B (arr w t) ∧
          v.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ v.gpr .r9 = s.gpr .r9 ∧ v.mem = u.mem) ∧ Keep [.r8] u v := by
      refine WP.keep _ ?_ (by decide)
      prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide),
        ku.gpr (r := .r9) (by decide), p5, p6, p7, x9, (hx0.of_keep ku).r29, BitVec.ofNat_add]
    rw [WP.seq_iff]
    refine WP.mono hb fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
    obtain k₁ : Keep [.r0, .r5, .r6, .r7, .r8] s v := ((kx.trans ku).trans kv).mono (by decide)
    obtain hv : Ws v B Z w N := h.of_keep k₁
    refine WP.mono (selLoop_ok hv.scr v5 v6 v7 v8 (by rw [v9, h9]) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (Nat.le_refl _)) (ahead1_of_ne hrt)) ?_
    intro y ⟨vv, out, ky⟩
    rw [vm, mu, mx] at vv out
    exact ⟨hv.of_keep ky, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
      (by omega_arith) (by simp), vv, (k₁.trans ky).mono (by decide)⟩

/-- The quotient bit and the mask: from the borrow `β` in `r9`, `r10 = 1 - β` and
`r9` the mask of `β = 0`. -/
theorem bit_ok {s : State} (b9 : (s.gpr .r9).toNat ≤ 1) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.Div.bit) s fun u =>
      (u.gpr .r10 = BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) ∧
        u.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) ∧
        u.mem = s.mem) ∧ Keep [.r0, .r9, .r10] s u := by
  obtain e : BitVec.ofNat 64 1 ^^^ s.gpr .r9 = BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) := by
    rcases (show (s.gpr .r9).toNat = 0 ∨ (s.gpr .r9).toNat = 1 by omega_arith) with z | z
    · have : s.gpr .r9 = 0 := BitVec.eq_of_toNat_eq z
      rw [this]; rfl
    · have : s.gpr .r9 = 1 := BitVec.eq_of_toNat_eq z
      rw [this]; rfl
  refine WP.keep _ ?_ (by decide)
  prun [VG.Impl.Rsa.PPC64LE.Div.bit, e]

/-- An even digit or'ed with a bit is their sum. -/
theorem or_bit_arith (x : BitVec 32) (c : BitVec 64) (hx : x.toNat % 2 = 0) (hc : c.toNat ≤ 1) :
    ((x.setWidth 64 ||| c).setWidth 32).toNat = x.toNat + c.toNat := by
  have h := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_ext32,
    show x.toNat = 2 ^ 1 * (x.toNat / 2) by omega_arith,
    ← Nat.two_pow_add_eq_or_of_lt (show c.toNat < 2 ^ 1 by omega_arith)]
  omega_arith

/-- `setBit q`: the bit in `r10` added to the even `[q]`, and `r4` decremented. -/
theorem setBit_ok {s : State} {B : Addr} {Z w N q : Nat} (h : Ws s B Z w N) (hq : q < N)
    (hN : N ≤ 256) (even : num s.mem B w q % 2 = 0) (b10 : (s.gpr .r10).toNat ≤ 1) :
    WP isa (.block (setBit q)) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q] [] s.mem u.mem ∧
      num u.mem B w q = num s.mem B w q + (s.gpr .r10).toNat ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep [.r0, .r4, .r5] s u := by
  obtain fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  unfold setBit
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  obtain hb : WP isa (.block [.load .w .r0 .r5 0, .logic .or .r0 .r0 .r10, .store .w .r0 .r5 0,
      .subi .r4 .r4 1]) (s.write .r5 (off B (arr w q))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w q))
          (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) ∧
          u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r4] (s.write .r5 (off B (arr w q))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.scr.ld (show arr w q + 4 ≤ Z by omega_arith), h.scr.st (show arr w q + 4 ≤ Z by omega_arith)]
  refine WP.mono hb fun u ⟨⟨mu, u4⟩, ku⟩ => ?_
  obtain kt : Keep [.r0, .r4, .r5] s u := ((Keep.write _ _ _).trans ku).mono
  obtain o := writeW32_outside s.mem B (d := arr w q)
    (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) (by omega_arith)
  obtain e0 := VG.Proof.Rsa.KeyWorkspace.num_mod2 s.mem B (w := w) (j := q) (by omega_arith)
  obtain e32 := VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem B (w := w) (j := q) (by omega_arith)
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat % 2 at e0
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat at e32
  refine ⟨h.of_keep kt, ?_, ?_, u4, kt⟩
  · rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega_arith) (by simp)
  · rw [mu, VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ (by omega_arith) (by omega_arith),
      or_bit_arith _ _ (by omega_arith) b10]
    have := Nat.mod_add_div (num s.mem B w q) (2 ^ 32)
    omega_arith

end VG.Proof.Rsa.PPC64LE.Keys

end

end

/-!
# The division of the RSA key operations on PPC64LE

`step_ok`: a step of `div q r d t` is `Proof/Rsa/KeyMath.lean`'s `divStep`
of the divisor `D = [d]` (its `w + 1` digits) and `K = 32 w`, on the
quotient `[q]` and the remainder `[r]` (its `w + 1` digits), when `D > 0`;
for `D = 0` it runs all the same. `div_ok`: the `32 w` steps from `(0, N)`,
the quotient `N / D` and the remainder `N mod D`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Proof.Rsa (divStep divIter divIter_inv divIter_done borrow_iff)
open VG.Impl.Rsa.PPC64LE.Div (div init step)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj ranges)

/-- The `w + 1` digits of an array outside the frame. -/
theorem keep_num1 {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) (fit : arr w j + S w ≤ 2 ^ 64) : num1 m' B w j = num1 m B w j := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega_arith)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; simp only [S] at *; omega_arith
  · have := hd d hd'; have : 160 ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- The registers a step changes. -/
abbrev stepRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The numbers of a step: from the shift's equations and the subtraction's,
the step is `divStep`. -/
theorem step_arith {D R Q Q1 R1 T c c' β P1 P2 H : Nat} (hD : 0 < D) (hR : R < D)
    (hDP : D < P1) (hP1 : P1 = 2 * H) (hP2 : P2 = 4294967296 * P1) (hQ1 : Q1 < P1) (hT : T < P2)
    (hc : c ≤ 1) (hβ : β ≤ 1) (e1 : Q1 + P1 * c = 2 * Q) (e2 : R1 + P2 * c' = 2 * R + c)
    (e3 : T + D = R1 + P2 * β) :
    R1 = 2 * R + Q / H ∧ Q1 = 2 * Q % P1 ∧ (β = 0 ↔ D ≤ R1) ∧ (β = 0 → T = R1 - D) := by
  obtain hH : 0 < H := by omega_arith
  obtain hc' : c' = 0 := by
    rcases Nat.eq_zero_or_pos c' with z | z
    · exact z
    · have : P2 ≤ P2 * c' := Nat.le_mul_of_pos_right _ z
      omega_arith
  subst hc'
  obtain hcQ : c = Q / H := by
    have : 2 * Q / P1 = c := by
      rw [← e1, Nat.add_mul_div_left _ _ (by omega_arith), Nat.div_eq_of_lt hQ1, Nat.zero_add]
    rw [← this, hP1, Nat.mul_div_mul_left _ _ (by decide)]
  obtain hmod : Q1 = 2 * Q % P1 := by
    rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ1]
  obtain hb := borrow_iff e3 hT hβ
  refine ⟨by omega_arith, hmod, hb, fun h0 => ?_⟩
  rw [h0, Nat.mul_zero, Nat.add_zero] at e3
  omega_arith

/-- A step of the division. -/
theorem step_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    {D N₀ k : Nat} (hk : k < 32 * w) (hN₀ : N₀ < 2 ^ (32 * w)) (hD : num1 s.mem B w d = D)
    (hDw : D < 2 ^ (32 * w))
    (vals : 0 < D → num s.mem B w q = (divIter D (32 * w) k (0, N₀)).2 ∧
      num1 s.mem B w r = (divIter D (32 * w) k (0, N₀)).1) :
    WP isa (step q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep stepRegs s u ∧
      (0 < D → num u.mem B w q = (divIter D (32 * w) (k + 1) (0, N₀)).2 ∧
        num1 u.mem B w r = (divIter D (32 * w) (k + 1) (0, N₀)).1) := by
  obtain fq := h.arr_fit hq
  obtain fr := h.arr_fit hr
  obtain fd := h.arr_fit hd
  obtain ft := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  rw [step, WP.seq_iff]
  refine WP.mono (shift_ok h hq hr hN hqr) fun s1 ⟨h1, km1, ⟨c, hc, eq1, c', hc', er1⟩, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subtract_ok h1 hr hd ht hN (Ne.symm hrt) (Ne.symm hdt))
    fun s2 ⟨h2, km2, eT, hβ, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (bit_ok hβ) fun s3 ⟨⟨r10, r9, m3⟩, k3⟩ => ?_
  obtain h3 : Ws s3 B Z w N := h2.of_keep k3
  rw [WP.seq_iff]
  refine WP.mono (keep_ok h3 hr ht hN hrt (b := decide ((s2.gpr .r9).toNat = 0))
    (by rw [r9]; by_cases z : (s2.gpr .r9).toNat = 0 <;> simp [z])) fun s4 ⟨h4, km4, eR, k4⟩ => ?_
  obtain e10 : s4.gpr .r10 = s3.gpr .r10 := k4.gpr _ (by decide)
  -- The quotient after the shift, through the subtraction and the selection.
  obtain q2 : num s2.mem B w q = num s1.mem B w q :=
    KeyWorkspace.Keep.num km2 (by simp; omega_arith) (by simp) (by omega_arith)
  obtain q4 : num s4.mem B w q = num s1.mem B w q := by
    rw [KeyWorkspace.Keep.num km4 (by simp; omega_arith) (by simp) (by omega_arith), m3, q2]
  obtain even : num s4.mem B w q % 2 = 0 := by
    rw [q4]
    have : 2 ∣ 2 ^ (32 * w) * c :=
      Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.pow_mod 2 (32 * w) 2 ▸ by
        rw [Nat.mod_self, Nat.zero_pow (by omega_arith)])) _
    omega_arith
  refine WP.mono (setBit_ok h4 hq hN even (by rw [e10, r10]; split <;> decide))
    fun u ⟨hu, km5, eQ, u4, k5⟩ => ?_
  obtain kr : Keep stepRegs s u := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  obtain k12 : KeyWorkspace.Keep B w [q, r, t] [] s.mem s2.mem := KeyWorkspace.Keep.join km1 km2
  obtain k45 : KeyWorkspace.Keep B w [q, r, t] [] s2.mem u.mem := by
    rw [← m3]; exact KeyWorkspace.Keep.join km4 km5
  refine ⟨hu, k12.trans k45, ?_, kr, fun hD0 => ?_⟩
  · rw [u4, k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  · obtain ⟨vq, vr⟩ := vals hD0
    obtain ⟨_, hR, -, -, -⟩ := divIter_inv hD0 hN₀ k (by omega_arith)
    have es : divIter D (32 * w) (k + 1) (0, N₀) = divStep D (32 * w) (divIter D (32 * w) k (0, N₀)) := rfl
    -- The divisor and the shifted remainder, through the writes.
    obtain d1 : num1 s1.mem B w d = D := by
      rw [keep_num1 km1 (by simp; omega_arith) (by simp) (by omega_arith), hD]
    obtain d2 : num1 s2.mem B w d = D := by
      rw [keep_num1 km2 (by simp; omega_arith) (by simp) (by omega_arith), d1]
    obtain r2 : num1 s2.mem B w r = num1 s1.mem B w r := keep_num1 km2 (by simp; omega_arith) (by simp) (by omega_arith)
    obtain t3 : num1 s3.mem B w t = num1 s2.mem B w t := by rw [m3]
    obtain ur : num1 u.mem B w r = num1 s4.mem B w r := keep_num1 km5 (by simp; omega_arith) (by simp) (by omega_arith)
    obtain hP2 : 2 ^ (32 * (w + 1)) = 4294967296 * 2 ^ (32 * w) := by
      rw [show 32 * (w + 1) = 32 + 32 * w by omega_arith, Nat.pow_add]
    obtain hP1 : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, 32 * w = j + 1 := ⟨32 * w - 1, by omega_arith⟩
      rw [hj, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    obtain hQ1 : num s1.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
    obtain hT : num1 s2.mem B w t < 2 ^ (32 * (w + 1)) := val32_lt _ _ _ _
    rw [d1] at eT
    obtain hR' : num1 s.mem B w r < D := by rw [vr]; exact hR
    obtain ⟨eR1, eQ1, hb, hTv⟩ := step_arith hD0 hR' hDw hP1 hP2 hQ1 hT hc hβ eq1 er1 eT
    obtain ep : divIter D (32 * w) k (0, N₀) = (num1 s.mem B w r, num s.mem B w q) :=
      Prod.ext vr.symm vq.symm
    rw [es, ep]
    simp only [divStep]
    rw [ur, eR, t3, m3, r2, eQ, e10, r10, q4, ← eR1, ← eQ1]
    by_cases hl : num1 s1.mem B w r < D
    · have hβ1 : (s2.gpr .r9).toNat ≠ 0 := fun z => absurd (hb.mp z) (by omega_arith)
      simp only [hl, hβ1, ↓reduceIte, decide_false]
      exact ⟨by simp, rfl⟩
    · have hβ0 : (s2.gpr .r9).toNat = 0 := hb.mpr (by omega_arith)
      simp only [hl, hβ0, ↓reduceIte, decide_true]
      exact ⟨by simp, hTv hβ0⟩

/-- `init r`: the remainder's `w + 1` digits := 0, and `32 w` steps to count in `r4`. -/
theorem init_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 256) :
    WP isa (init r) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = 0 ∧ u.gpr .r4 = BitVec.ofNat 64 (32 * w) ∧ Keep [.r0, .r4, .r5, .r8] s u := by
  obtain fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [init, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) ?_
  obtain hb : WP isa (.block [.addi .r8 .r29 1, .li .r0 0]) (s.write .r5 (off B (arr w r))) fun u =>
      (u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .r0 = 0 ∧
        u.mem = s.mem) ∧ Keep [.r0, .r8] (s.write .r5 (off B (arr w r))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r29, BitVec.ofNat_add]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u8, u0, mu⟩, ku⟩ => ?_
  obtain k₁ : Keep [.r0, .r4, .r5, .r8] s u := ((Keep.write _ _ _).trans ku).mono
  obtain hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (zeroLoop_ok hu.scr u5 u8 u0 (by omega_arith) (by omega_arith) (by omega_arith)) fun v ⟨z, out, kv⟩ => ?_
  obtain hv : Ws v B Z w N := hu.of_keep kv
  obtain hl : WP isa (.block [.lsl .r4 .r29 5]) v fun x =>
      (x.gpr .r4 = BitVec.ofNat 64 (32 * w) ∧ x.mem = v.mem) ∧ Keep [.r4] v x := by
    refine WP.keep _ ?_ (by decide)
    obtain e : BitVec.ofNat 64 w <<< 5 = BitVec.ofNat 64 (32 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    prun [hv.r29, e]
  refine WP.mono hl fun x ⟨⟨x4, xm⟩, kx⟩ => ⟨hv.of_keep kx, ?_, ?_, x4, (k₁.trans (kv.trans kx)).mono⟩
  · rw [xm, ← mu]
    exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out) (by omega_arith) (by simp)
  · rw [xm]
    exact Proof.Bignum.PPC64LE.val32_zero fun j hj => z j hj

/-- `div q r d t`: `[q] := [q] / [d]` and the `w + 1` digits of `[r]` := `[q] mod [d]`,
for a divisor whose extra digit is 0, when it is not 0. -/
theorem div_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hdz : w32 s.mem B (arr w d + 4 * w) = 0) :
    WP isa (div q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      Keep stepRegs s u ∧
      (0 < num s.mem B w d → num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d) := by
  obtain fd := h.arr_fit hd
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  -- The divisor's `w + 1` digits are its number.
  obtain hD : num1 s.mem B w d = num s.mem B w d := by
    obtain e := val32_append s.mem B (arr w d) w 1
    obtain e1 : val32 s.mem B (arr w d + 4 * w) 1 = 0 := by
      simp only [val32, hdz, Nat.mul_zero, Nat.add_zero]
    change val32 _ _ _ (w + 1) = val32 _ _ _ w
    rw [e, e1, Nat.mul_zero, Nat.add_zero]
  obtain hDw : num s.mem B w d < 2 ^ (32 * w) := val32_lt _ _ _ _
  obtain hN₀ : num s.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
  rw [div, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u4, ku⟩ => ?_
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem x.mem ∧ Keep stepRegs s x ∧
      (0 < D → num x.mem B w q = (divIter D (32 * w) i (0, N₀)).2 ∧
        num1 x.mem B w r = (divIter D (32 * w) i (0, N₀)).1)
  obtain i0 : Inv 0 u := ⟨hu, km.mono, ku.mono, fun _ => ⟨KeyWorkspace.Keep.num km (by simp; omega_arith)
    (by simp) (by have := h.fit64 hq; omega_arith), z⟩⟩
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := step q r d t) (cnt := .r4) (N := 32 * w)
    (by omega_arith) (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, vx⟩ _ => ?_) i0 u4) fun x ⟨hx, kx, rx, vx⟩ => ?_
  · have dx : num1 x.mem B w d = D := by
      rw [keep_num1 kx (by simp; omega_arith) (by simp) (by omega_arith), hD]
    refine WP.mono (step_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt hi hN₀ dx hDw vx)
      fun y ⟨hy, ky, y4, ry, vy⟩ => ⟨⟨hy, kx.trans ky, rx.trans' ry, vy⟩, y4⟩
  · refine ⟨hx, kx, rx, fun hD0 => ?_⟩
    obtain ⟨e1, e2⟩ := vx hD0
    rw [divIter_done hD0 hN₀] at e1 e2
    exact ⟨e1, e2⟩

end VG.Proof.Rsa.PPC64LE.Keys
