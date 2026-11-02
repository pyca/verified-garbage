module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The ARMv7 key stages: steps around Montgomery multiplication

`MR.of_keep`: a step of the key working space that writes none of the arrays
16–20 keeps Montgomery multiplication ready; `keep_of_mont`: a
multiplication writes the key arrays of its own and its result's arrays;
`clrTop_ok`: `clrTop j` clears the two top words of array `j`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- `a - k` added to a pointer, with no borrow. -/
theorem add_ofNat_sub32 (x : BitVec 32) {a k : Nat} (hk : k ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 k = x + BitVec.ofNat 32 (a - k) := by
  rw [show a = (a - k) + k by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    show a - k + k - k = a - k by omega]

/-- `clrTop j`: the two top words of `[j]` cleared. -/
theorem clrTop_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hw : 2 ≤ w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = val32 s.mem (State.addr B) (arr w j) (w - 2) → Rest opRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (clrTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold clrTop
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * (w - 2)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [this, BitVec.add_assoc, ← BitVec.ofNat_add,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_sub32 _ (by omega)]
    congr 2; omega
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N :=
    ((h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have a0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * (w - 2)) := by
    rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_str (by decide) a0 (h4.write (by omega)) fun s5 u5 => ?_
  have h5 := h4.of_mupd u5
  have a4 : State.addr (s5.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr B) (arr w j + 4 * (w - 2) + 4) := by
    rw [u5.gpr, u4.other _ (by decide), e3, BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.addr (by omega)
  refine wp_str (by decide) a4 (h5.write (by omega)) fun t u6 => ?_
  have ht := h5.of_mupd u6
  have z4 : s4.gpr .r1 = 0 := u4.gpr
  have mt : t.mem = (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32)).writeW
      (off (State.addr B) (arr w j + 4 * (w - 2) + 4)) (0 : BitVec 32) := by
    rw [u6.mem, u5.gpr, z4, u5.mem, z4, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * (w - 2)) (0 : BitVec 32) (by omega)
  have o2 := writeW32_outside (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32))
    (State.addr B) (d := arr w j + 4 * (w - 2) + 4) (0 : BitVec 32) (by omega)
  rw [← mt] at o2
  refine k t ht ?_ ?_ ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest _).trans (u6.rest _))))))
  · exact (Keep.of_arr (d := 4 * (w - 2)) o1 (by omega) (by simp)).trans
      (Keep.of_arr (d := 4 * (w - 2) + 4) (by simpa only [Nat.add_assoc] using o2) (by omega) (by simp))
  · change val32 _ _ _ _ = _
    have e := val32_append t.mem (State.addr B) (arr w j) (w - 2) 2
    rw [show w - 2 + 2 = w by omega] at e
    have t0 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) = 0 := by
      simp only [w32]
      rw [mt, Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep _ (d := arr w j + 4 * (w - 2)) (n := 4)
        (e := arr w j + 4 * (w - 2) + 4) (k := 4) (Or.inl (Nat.le_refl _)) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32]; rfl
    have t1 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2) + 4) = 0 := by
      simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl
    have top : val32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) 2 = 0 := by
      simp only [val32, t0, t1]
    rw [e, top, Nat.mul_zero, Nat.add_zero]
    exact (o2.val32 (by omega) (by omega)).trans (o1.val32 (by omega) (by omega))

end VG.Proof.Rsa.Arm.Recover
