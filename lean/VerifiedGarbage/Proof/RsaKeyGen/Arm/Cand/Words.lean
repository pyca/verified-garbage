module
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs

import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Framework.Block

/-! # A candidate on ARMv7: a high word of an array changed

`hiOp_ok`: word `i` of `[j]`, at byte `4 W − c`, read into `r1`, changed by
`ops` and stored back (`topBits`, `clrTopBit`); `val32_write_any`: a word
written into a number of words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- Word `i` of a number of `k` words. -/
theorem val32_word (m : Mem) (base : Addr) {d k i : Nat} (hi : i < k) :
    w32 m base (d + 4 * i) = val32 m base d k / 2 ^ (32 * i) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega⟩
  rw [val32_append m base d i (r + 1)]
  simp only [val32]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hw]

/-- Word `i` of a number written. -/
theorem val32_write_any (m : Mem) (base : Addr) {d k i : Nat} (v : BitVec 32) (hi : i < k)
    (fit : d + 4 * k ≤ 2 ^ 64) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d k =
      val32 m base d k % 2 ^ (32 * i) + 2 ^ (32 * i) * v.toNat + 2 ^ (32 * (i + 1)) * (val32 m base d k / 2 ^ (32 * (i + 1))) := by
  have o := writeW32_outside m base (d := d + 4 * i) v (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega⟩
  rw [val32_append _ base d i (r + 1), val32_append m base d i (r + 1)]
  simp only [val32]
  have e1 : val32 (m.writeW (off base (d + 4 * i)) v) base d i = val32 m base d i := o.val32 (by omega) (by omega)
  have e2 : w32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i) = v.toNat := by
    simp only [w32]; rw [Mem.readW_writeW_self32]
  have e3 : val32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i + 4) r = val32 m base (d + 4 * i + 4) r :=
    o.val32 (by omega) (by omega)
  rw [e1, e2, e3]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  have hq : 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2 ^ 32 := by rw [← Nat.pow_add]; congr 1
  generalize val32 m base d i = L at *
  generalize w32 m base (d + 4 * i) = x at *
  generalize val32 m base (d + 4 * i + 4) r = T
  have hmod : (L + 2 ^ (32 * i) * (x + 2 ^ 32 * T)) % 2 ^ (32 * i) = L := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo]
  have hdiv : (L + 2 ^ (32 * i) * (x + 2 ^ 32 * T)) / 2 ^ (32 * (i + 1)) = T := by
    rw [hq, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hw, Nat.zero_add]
  rw [hmod, hdiv, hq, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Word `i` of `[j]`, at byte `4 W − c`, into `r1` and back, through `f`. -/
theorem hiOp_ok {s : State} {B : BitVec 32} {Z w N j c i : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hc : encodable (BitVec.ofNat 32 c) = true) (hi : w * 4 = 4 * i + c)
    (hiw : i < w) {ops rest : List Instr} {Q : State → Prop} {f : BitVec 32 → BitVec 32}
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = num s.mem B w j % 2 ^ (32 * i) +
        2 ^ (32 * i) * (f (BitVec.ofNat 32 (num s.mem B w j / 2 ^ (32 * i) % 2 ^ 32))).toNat +
        2 ^ (32 * (i + 1)) * (num s.mem B w j / 2 ^ (32 * (i + 1))) →
      Rest [.r0, .r1] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) :: .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)) ::
      .ldr .r1 .r0 0 :: (ops ++ .str .r1 .r0 0 :: rest))) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_lsl (by omega)) fun s2 u2 => ?_
  refine wp_dp (op2_imm hc) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * i) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (w * 2 ^ 2) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := w) (by omega)]
    rw [this, BitVec.add_assoc, BitVec.ofNat_add_ofNat, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega)]
    congr 2; omega
  have h3 : Ws s3 B Z w N :=
    (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  have a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * i) := by
    rw [e3, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_ldr (by decide) a0 (h3.read (by omega)) fun s4 u4 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hops s4 _ fun u' x => x) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := (h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide)
    (by decide) (by decide)
  have a5 : State.addr (s5.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * i) := by
    rw [u5.other _ (by decide), u4.other _ (by decide)]; exact a0
  refine wp_str (by decide) a5 (h5.write (by omega)) fun t u6 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * i)) (s5.gpr .r1) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * i) (s5.gpr .r1) (by omega)
  rw [← mt] at o1
  refine k t (h5.of_mupd u6) (Keep.of_arr (d := 4 * i) o1 (by omega) (by simp)) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest _))))))
  have v4 : s4.gpr .r1 = BitVec.ofNat 32 (num s.mem B w j / 2 ^ (32 * i) % 2 ^ 32) := by
    rw [u4.gpr, u3.mem, u2.mem, m1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
    exact val32_word s.mem (State.addr B) hiw
  change val32 _ _ _ _ = _
  rw [mt, val32_write_any _ _ _ hiw (by omega), u5.gpr, v4]

end VG.Proof.RsaKeyGen.Arm.Cand
