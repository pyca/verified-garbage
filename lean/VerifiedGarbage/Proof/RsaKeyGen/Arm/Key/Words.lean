module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Key
import VerifiedGarbage.Proof.Mont.WriteWord32
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2

/-! # An RSA key on ARMv7: a word of an array set

`setWd j o x` and `setHi j sh c x` store `x` to word `i` of array `j`, at
byte `4 i` (`o`, or `(W << sh) − c`): for an array below `2^(32 i)`, its
number grows by `x 2^(32 i)` (`setWd_ok`, `setHi_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- Word `i` written, of a number below `2^(32 i)`. -/
theorem val32_write_word (m : Mem) (base : Addr) {d i k : Nat} (v : BitVec 32) (hi : i < k)
    (fit : d + 4 * k ≤ 2 ^ 64) (hl : val32 m base d k < 2 ^ (32 * i)) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d k = val32 m base d k + 2 ^ (32 * i) * v.toNat :=
  VG.Proof.Mont.val32_write_word m base v hi fit hl

/-- `setWd j o x`: word `o / 4` of `[j]` := `x`. -/
theorem setWd_ok {s : State} {B : BitVec 32} {Z w N j o x : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (ho : o % 4 = 0) (how : o / 4 < w) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hl : num s.mem B w j < 2 ^ (32 * (o / 4))) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = num s.mem B w j + 2 ^ (32 * (o / 4)) * (x % 2 ^ 32) →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setWd j o x ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold setWd
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm hx) fun s2 u2 => ?_
  have h2 : Ws s2 B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  have a0 : State.addr (s2.gpr .r0 + BitVec.ofNat 32 o) = off (State.addr B) (arr w j + 4 * (o / 4)) := by
    rw [u2.other _ (by decide), p1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [show arr w j + o = arr w j + 4 * (o / 4) by omega]
    exact h.addr (by omega)
  refine wp_str (by omega) a0 (h2.write (by omega)) fun t u3 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * (o / 4))) (BitVec.ofNat 32 x) := by
    rw [u3.mem, u2.gpr, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * (o / 4)) (BitVec.ofNat 32 x) (by omega)
  rw [← mt] at o1
  refine k t (h2.of_mupd u3) (Keep.of_arr (d := 4 * (o / 4)) o1 (by omega) (by simp)) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _)))
  change val32 _ _ _ _ = _
  rw [mt, val32_write_word _ _ _ how (by omega) hl, BitVec.toNat_ofNat]

/-- `setHi j sh c x`: the word at byte `(w << sh) − c` of `[j]`, word `i`, := `x`. -/
theorem setHi_ok {s : State} {B : BitVec 32} {Z w N j sh c x i : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hsh : 1 ≤ sh ∧ sh ≤ 2) (hc : encodable (BitVec.ofNat 32 c) = true)
    (hx : encodable (BitVec.ofNat 32 x) = true) (hi : w * 2 ^ sh = 4 * i + c) (hiw : i < w)
    (hl : num s.mem B w j < 2 ^ (32 * i)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = num s.mem B w j + 2 ^ (32 * i) * (x % 2 ^ 32) →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setHi j sh c x ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  have p4 : 2 ^ sh ≤ 4 := by
    rcases hsh with ⟨h1, h2⟩
    rcases (by omega : sh = 1 ∨ sh = 2) with rfl | rfl <;> decide
  unfold setHi
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by omega)) fun s2 u2 => ?_
  refine wp_dp (op2_imm hc) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * i) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< sh = BitVec.ofNat 32 (w * 2 ^ sh) := by
      apply BitVec.eq_of_toNat_eq
      have : w * 2 ^ sh ≤ w * 4 := Nat.mul_le_mul_left _ p4
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := w) (by omega)]
    rw [this, BitVec.add_assoc, BitVec.ofNat_add_ofNat, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega)]
    congr 2; omega
  refine wp_mov (op2_imm hx) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N :=
    ((h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have a0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * i) := by
    rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_str (by decide) a0 (h4.write (by omega)) fun t u5 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * i)) (BitVec.ofNat 32 x) := by
    rw [u5.mem, u4.gpr, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * i) (BitVec.ofNat 32 x) (by omega)
  rw [← mt] at o1
  refine k t (h4.of_mupd u5) (Keep.of_arr (d := 4 * i) o1 (by omega) (by simp)) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest _)))))
  change val32 _ _ _ _ = _
  rw [mt, val32_write_word _ _ _ hiw (by omega) hl, BitVec.toNat_ofNat]

end VG.Proof.Rsa.Arm.Keys
