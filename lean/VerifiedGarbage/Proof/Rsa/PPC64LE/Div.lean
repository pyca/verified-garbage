module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
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
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps

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

/-- The pointer of an array into `r5` and the count `w + c` into `r8`, for
the loops of the division. -/
theorem ptrCount_ok {s : State} {B : Addr} {Z w N j c : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hc : c ≤ 1) {extra : List Instr} {Q : State → Prop}
    (hx : extra = [.addi .r8 .r29 c] ∨ extra = [.addi .r8 .r29 c, .li .r9 0])
    (k : ∀ u, u.gpr .r5 = off B (arr w j) → u.gpr .r8 = BitVec.ofNat 64 (w + c) →
      (extra.length = 2 → u.gpr .r9 = 0) → (extra.length = 1 → u.gpr .r9 = s.gpr .r9) →
      u.mem = s.mem → Keep [.r5, .r8, .r9] s u → Q u) :
    WP isa (.block (ptr .r5 j ++ extra)) s Q := by
  have := h.wle
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have h1 : Ws (s.write .r5 (off B (arr w j))) B Z w N := h.of_keep (Keep.write _ _ _)
  rcases hx with rfl | rfl
  · refine WP.mono (WP.keep [.r8] (Q := fun u => u.gpr .r5 = off B (arr w j) ∧
      u.gpr .r8 = BitVec.ofNat 64 (w + c) ∧ u.gpr .r9 = s.gpr .r9 ∧ u.mem = s.mem) ?_ (by rfl))
      fun u ⟨⟨u5, u8, u9, um⟩, ku⟩ => k u u5 u8 (by simp) (fun _ => u9) um
        (((Keep.write _ _ _).trans ku).mono)
    prun [h.r29, exec_addi (show Reg.r29 ≠ .r0 by decide) (show c < 2 ^ 15 by omega_arith),
      BitVec.ofNat_add]
  · refine WP.mono (WP.keep [.r8, .r9] (Q := fun u => u.gpr .r5 = off B (arr w j) ∧
      u.gpr .r8 = BitVec.ofNat 64 (w + c) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem) ?_ (by rfl))
      fun u ⟨⟨u5, u8, u9, um⟩, ku⟩ => k u u5 u8 (fun _ => u9) (by simp) um
        (((Keep.write _ _ _).trans ku).mono)
    prun [h.r29, exec_addi (show Reg.r29 ≠ .r0 by decide) (show c < 2 ^ 15 by omega_arith),
      BitVec.ofNat_add]
    rfl

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
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have dqr := arr_disj (w := w) hqr
  rw [shift, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w q))) := (Keep.write _ _ _).mono
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r5 = off B (arr w q) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem)
    (by prun; rfl) (by decide)) fun u ⟨⟨u5, u9, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := k₀.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  -- The quotient: `[q]' + 2^(32 w) c = 2 [q]`, and the rest after it.
  have rest : ∀ v : State, Ws v B Z w N → Keep opRegs s v → (v.gpr .r9).toNat ≤ 1 →
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
    have k₁v : KeyWorkspace.Keep B w [q, r] [] s.mem v.mem :=
      KeyWorkspace.Keep.of_arr (d := 0) (by simpa using vout) (by omega_arith) (by simp)
    have rr : num1 v.mem B w r = num1 s.mem B w r := vout.val32 (by omega_arith) (by omega_arith)
    rw [WP.seq_iff, ← List.append_nil (ptr .r5 r)]
    refine ptr_ok hv (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
    have hx0 : Ws (v.write .r5 (off B (arr w r))) B Z w N := hv.of_keep (Keep.write _ _ _)
    have x9 : (v.write .r5 (off B (arr w r))).gpr .r9 = v.gpr .r9 := rfl
    refine evenW_ok hx0 (fun hev x mx kx => ?_) (fun hodd x mx kx => ?_)
    · have x5 : x.gpr .r5 = off B (arr w r) := by rw [kx.gpr _ (by decide)]; rfl
      have hx := hx0.of_keep kx
      rw [WP.seq_iff]
      refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
        y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = v.gpr .r9 ∧ y.mem = v.mem)
        (by prun [x5, hx.r29, kx.gpr (r := .r9) (by decide), x9, mx, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)])
        (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
      have hy := hx.of_keep ky
      rw [WP.seq_iff]
      refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith) (by omega_arith))
        fun z ⟨c9', zr, zout, kz, z5⟩ => ?_
      have hz := hy.of_keep kz
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
        have zn : num t.mem B w r = num z.mem B w r := by
          rw [tm]; exact (writeW32_outside z.mem B vd (d := arr w r + 4 * w) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
        have zw : w32 t.mem B (arr w r + 4 * w) = vd.toNat := by rw [tm, w32_write_self]
        rw [zt] at td
        rw [y9, ym, show 64 * (w / 2) = 32 * w by omega_arith, ← num_words _ _ hev, ← num_words _ _ hev] at zr
        rw [← rr, num1_eq, num1_eq, zn, zw, show 2 ^ (32 * (w + 1)) = 2 ^ (32 * w) * 2 ^ 32 by
          rw [← Nat.pow_add]; congr 1]
        generalize 2 ^ (32 * w) = P at *
        grind
      · exact Keep.mono (rs' := opRegs) (((((kv.trans (Keep.write _ _ _)).trans kx).trans ky).trans kz).trans kt)
          (by decide)
    · have x5 : x.gpr .r5 = off B (arr w r) := by rw [kx.gpr _ (by decide)]; rfl
      have hx := hx0.of_keep kx
      rw [WP.seq_iff]
      refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
        y.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ y.gpr .r9 = v.gpr .r9 ∧ y.mem = v.mem)
        (by prun [x5, hx.r29, kx.gpr (r := .r9) (by decide), x9, mx, BitVec.ofNat_add])
        (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
      have hy := hx.of_keep ky
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
    have hy := hx.of_keep ky
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
    have hy := hx.of_keep ky
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
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  have dtr := arr_disj (w := w) htr
  have dtd := arr_disj (w := w) htd
  rw [subtract]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have hx0 : Ws x B Z w N := h.of_keep kx
  refine evenW_ok hx0 (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := hx0.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun x => x.gpr .r5 = off B (arr w t) ∧ x.gpr .r6 = off B (arr w r) ∧
      x.gpr .r7 = off B (arr w d) ∧ x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧
      x.ca = decide (2 ^ 64 ≤ (BitVec.ofNat 64 (w / 2)).toNat + (2 ^ 64 - 1 - (BitVec.ofNat 64 (w / 2)).toNat) + 1) ∧
      x.mem = u.mem) ?_ (by decide)) fun v ⟨⟨v5, v6, v7, v8, vc, vm⟩, kv⟩ => ?_
    · mcrun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide), p5, p6,
        p7, hu.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]
    have vc' : v.ca = true := by
      rw [vc]; exact decide_eq_true (by have := (BitVec.ofNat 64 (w / 2)).isLt; omega_arith)
    have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (subWLoop_ok hv.scr v5 v6 v7 v8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (aheadW hev (ahead_of_ne htr)) (aheadW hev (ahead_of_ne htd))) fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
    have hy := hv.of_keep ky
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
      have hry : w32 y.mem B (arr w r + 4 * w) = w32 s.mem B (arr w r + 4 * w) := by
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
    have k₁ : Keep opRegs s v := ((kx.trans ku).trans kv).mono (by decide)
    have hv : Ws v B Z w N := h.of_keep k₁
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
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  have drt := arr_disj (w := w) hrt
  rw [keep]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have hx0 : Ws x B Z w N := h.of_keep kx
  have x9 : x.gpr .r9 = s.gpr .r9 := kx.gpr _ (by decide)
  refine evenW_ok hx0 (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := hx0.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun v => v.gpr .r5 = off B (arr w r) ∧ v.gpr .r6 = off B (arr w r) ∧
      v.gpr .r7 = off B (arr w t) ∧ v.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ v.gpr .r9 = s.gpr .r9 ∧ v.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), ku.gpr (r := .r7) (by decide),
        ku.gpr (r := .r9) (by decide), p5, p6, p7, x9, hu.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)])
      (by decide)) fun v ⟨⟨v5, v6, v7, v8, v9, vm⟩, kv⟩ => ?_
    have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (selWLoop_ok (b := b) hv.scr v5 v6 v7 v8 (by rw [v9, h9]) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (.inl (Nat.le_refl _)) (aheadW hev (ahead_of_ne hrt))) fun y ⟨veq, yout, ky, y5, y6, y7⟩ => ?_
    have hy := hv.of_keep ky
    have y9 : y.gpr .r9 = s.gpr .r9 := (ky.gpr _ (by decide)).trans v9
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
      have hry : w32 y.mem B (arr w r + 4 * w) = w32 s.mem B (arr w r + 4 * w) := by
        rw [← mx, ← mu, ← vm]; exact yout.w32 (by omega_arith) (by omega_arith)
      have veq' : num y.mem B w r = if b then num s.mem B w t else num s.mem B w r := by
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
    have k₁ : Keep [.r0, .r5, .r6, .r7, .r8] s v := ((kx.trans ku).trans kv).mono (by decide)
    have hv : Ws v B Z w N := h.of_keep k₁
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
  have e : BitVec.ofNat 64 1 ^^^ s.gpr .r9 = BitVec.ofNat 64 (if (s.gpr .r9).toNat = 0 then 1 else 0) := by
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
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  unfold setBit
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  have hb : WP isa (.block [.load .w .r0 .r5 0, .logic .or .r0 .r0 .r10, .store .w .r0 .r5 0,
      .subi .r4 .r4 1]) (s.write .r5 (off B (arr w q))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w q))
          (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) ∧
          u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r4] (s.write .r5 (off B (arr w q))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.scr.ld (show arr w q + 4 ≤ Z by omega_arith), h.scr.st (show arr w q + 4 ≤ Z by omega_arith)]
  refine WP.mono hb fun u ⟨⟨mu, u4⟩, ku⟩ => ?_
  have kt : Keep [.r0, .r4, .r5] s u := ((Keep.write _ _ _).trans ku).mono
  have o := writeW32_outside s.mem B (d := arr w q)
    (((s.mem.readW (off B (arr w q)) 32).setWidth 64 ||| s.gpr .r10).setWidth 32) (by omega_arith)
  have e0 := VG.Proof.Rsa.KeyWorkspace.num_mod2 s.mem B (w := w) (j := q) (by omega_arith)
  have e32 := VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem B (w := w) (j := q) (by omega_arith)
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat % 2 at e0
  change _ = (s.mem.readW (off B (arr w q)) 32).toNat at e32
  refine ⟨h.of_keep kt, ?_, ?_, u4, kt⟩
  · rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega_arith) (by simp)
  · rw [mu, VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ (by omega_arith) (by omega_arith),
      or_bit_arith _ _ (by omega_arith) b10]
    have := Nat.mod_add_div (num s.mem B w q) (2 ^ 32)
    omega_arith

end VG.Proof.Rsa.PPC64LE.Keys
