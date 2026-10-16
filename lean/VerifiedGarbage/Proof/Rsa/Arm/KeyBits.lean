module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.ShiftRight
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The operations on the arrays of the working space: halving, low bits and slots -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

theorem or_one (n : Nat) : n ||| 1 = 2 * (n / 2) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * (n / 2) + 1) / 2 = n / 2 by omega]
    simp

theorem xor_one (n : Nat) : (2 * n + 1) ^^^ 1 = 2 * n := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * n + 1) / 2 = n by omega, show 2 * n / 2 = n by omega]
    simp

theorem bv_or_one (x : BitVec 32) : (x ||| (1 : BitVec 32)).toNat = 2 * (x.toNat / 2) + 1 := by
  rw [BitVec.toNat_or]; simp [or_one]

theorem bv_clr_one (x : BitVec 32) : ((x ||| (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * (x.toNat / 2) := by
  rw [BitVec.toNat_xor, BitVec.toNat_or]; simp [or_one, xor_one]

theorem bv_and_one (x : BitVec 32) : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

theorem bit_cases {x : BitVec 32} (h : x.toNat ≤ 1) : x = 0#32 ∨ x = (1 : BitVec 32) := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with e | e
  · exact .inl (BitVec.eq_of_toNat_eq (by simp [e]))
  · exact .inr (BitVec.eq_of_toNat_eq (by simp [e]))

theorem bv_and_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x &&& y).toNat = if x.toNat = 1 ∧ y.toNat = 1 then 1 else 0 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

theorem bv_xor_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ^^^ y).toNat = (x.toNat + y.toNat) % 2 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

theorem bv_nor_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    ((x ||| y) ^^^ (1 : BitVec 32)).toNat = if x.toNat = 0 ∧ y.toNat = 0 then 1 else 0 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

/-- The address of the low word of array `j` in `r`. -/
theorem arr_addr0 {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) {r : Reg}
    (p : s.gpr r = B + BitVec.ofNat 32 (arr w j)) :
    State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr B) (arr w j) := by
  rw [p, Offset.add_add, Nat.add_zero]
  have := h.arr_fit hj
  exact h.addr (by simp only [S] at this; omega)

/-- A store to the low word of an array. -/
theorem num_write0 (m : Mem) (B : BitVec 32) {w j : Nat} (hw : 0 < w) (fit : arr w j + 4 * w ≤ 2 ^ 64)
    (v : BitVec 32) :
    num (m.writeW (off (State.addr B) (arr w j)) v) B w j = v.toNat + 2 ^ 32 * (num m B w j / 2 ^ 32) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have o := writeW32_outside m (State.addr B) (d := arr (k + 1) j) v (by omega)
  have tail := o.val32 (d := arr (k + 1) j + 4) (k := k) (by omega) (by omega)
  simp only [num] at tail ⊢
  rw [val32, val32, w32_write_self, tail]
  have : w32 m (State.addr B) (arr (k + 1) j) < 2 ^ 32 := (m.readW _ 32).isLt
  omega

theorem num_mod2 (m : Mem) (B : BitVec 32) {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 = w32 m (State.addr B) (arr w j) % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [num]; rw [val32]; omega

theorem num_mod32 (m : Mem) (B : BitVec 32) {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 ^ 32 = w32 m (State.addr B) (arr w j) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [num]; rw [val32]
  have : w32 m (State.addr B) (arr (k + 1) j) < 2 ^ 32 := (m.readW _ 32).isLt
  omega

/-- `half j`: `[j] = ([j] + r11 · 2^(32 w)) / 2`. -/
theorem half_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (bit : (s.gpr .r11).toNat ≤ 1) :
    WP isa (half j) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .r11).toNat) / 2 ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  rw [half, WP.seq_iff]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have a2 : State.addr (s2.gpr .r1 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * w) := by
    have e : s2.gpr .r1 = B + BitVec.ofNat 32 (arr w j + 4 * w) := by
      rw [u2.gpr, dpVal, p1]
      have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have := h.wle
        omega
      rw [h1.r9, this, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e, Offset.add_add, Nat.add_zero]
    exact h.addr (by omega)
  have h2 : Ws s2 B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_str (by decide) a2 (h2.write (by omega)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_mupd u3
  refine wp_mov (op2_reg _ _) fun u u4 => WP.block_nil ?_
  have hu : Ws u B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  have r11 : s3.gpr .r11 = s.gpr .r11 := by
    rw [u3.gpr, u2.other .r11 (by decide), r1.gpr _ (by decide)]
  have mu : u.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * w)) (s.gpr .r11) := by
    rw [u4.mem, u3.mem, u2.mem, m1, u2.other .r11 (by decide), r1.gpr _ (by decide)]
  have restU : Rest opRegs s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest _).trans (u4.rest (by simp))))
  have outS := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * w) (s.gpr .r11) (by omega)
  rw [← mu] at outS
  refine WP.mono (shiftRight_ok u (base := B) (size := Z) (o := arr w j) (n := w)
    ⟨nw, by omega, hu.writable⟩ h.wpos
    (by rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), p1])
    (by rw [u4.gpr, h3.r9])) ?_
  intro t inv
  have top : w32 u.mem (State.addr B) (arr w j + 4 * w) = (s.gpr .r11).toNat := by
    rw [mu, w32_write_self]
  have res := inv.result h.wpos (by rw [top]; exact bit)
  have low := outS.val32 (d := arr w j) (k := w) (by omega) (by omega)
  refine ⟨hu.rest inv.rest, (Keep.of_arr (d := 4 * w) outS (by omega) (by simp)).trans
    (Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside) (by omega) (by simp)),
    ?_, restU.trans (inv.rest.mono (by simp))⟩
  change val32 _ _ _ _ = _
  rw [res, low, top]

/-- `bitOf sl j`: the slot `sl` := the low bit of `[j]`. -/
theorem bitOf_ok {s : State} {B : BitVec 32} {Z w N j sl : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hsl : sl + 4 ≤ hdr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [] [sl] s.mem t.mem → slot t.mem B sl = num s.mem B w j % 2 →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf sl j ++ rest)) s Q := by
  unfold bitOf
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  have fit := h.arr_fit hj
  refine wp_ldr (by decide) (arr_addr0 h1 hj p1) (h1.read (by simp only [S] at fit; omega)) fun s2 u2 => ?_
  have h2 : Ws s2 B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_strSlot h3 hsl fun t u4 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) sl) (s3.gpr .r1) := by
    rw [u4.mem, u3.mem, u2.mem, m1]
  refine k t (h3.of_mupd u4) (by rw [mt]; exact keep_write _ _ (by simp) (by simp only [hdr] at hsl; omega))
    ?_ ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest _))))
  rw [mt, slot_write_self, u3.gpr, dpVal, u2.gpr, bv_and_one, m1, num_mod2 _ _ h.wpos]

/-- `andS d a b`: the slot `d` := the slots `a` and `b` and'ed. -/
theorem andS_ok {s : State} {B : BitVec 32} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ hdr) (ha : a + 4 ≤ hdr) (hb : b + 4 ≤ hdr)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  unfold andS
  refine wp_ldrSlot h ha fun s1 u1 => ?_
  have h1 : Ws s1 B Z w N := h.of_upd u1 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h1 hb fun s2 u2 => ?_
  have h2 : Ws s2 B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_strSlot h3 hd fun t u4 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) d) (s3.gpr .r1) := by
    rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine k t (h3.of_mupd u4) (by rw [mt]; exact keep_write _ _ (by simp) (by simp only [hdr] at hd; omega))
    ?_ ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest _))))
  rw [mt, slot_write_self, u3.gpr, dpVal, u2.gpr, u2.other .r1 (by decide), u1.gpr, u1.mem]
  exact bv_and_bits ba bb

end VG.Proof.Rsa.Arm.Keys
