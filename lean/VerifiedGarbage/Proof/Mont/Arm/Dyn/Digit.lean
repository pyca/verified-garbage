module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Arm.Words

import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: digits of a sum

A digit of `[a] + [b]` (`addDigitD_ok`) from the words in `r7` and `r2` and
the carry `r3`, stored at `[r8 + 4h]`, its carry to `r3`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg op2_lsr dpVal
  toNat_add_lt toNat_shr)

theorem toNat_ofNat_dig (h : Nat) (w : Nat) : (BitVec.ofNat 32 (hdig w h)).toNat = hdig w h := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hdig_lt _ _) (by decide))]

theorem toNat_add_eq {a b : BitVec 32} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y) (h : x + y < 2 ^ 32) :
    (a + b).toNat = x + y := by
  rw [toNat_add_lt (by rw [ha, hb]; exact h), ha, hb]

theorem toNat_sub_eq {a b : BitVec 32} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y) (h : y ≤ x) :
    (a - b).toNat = x - y := by
  rw [VG.Proof.X25519.Arm.toNat_sub_le (by rw [ha, hb]; exact h), ha, hb]

/-- A digit's sum, masked to its low half. -/
theorem and_mask_ofNat {x : BitVec 32} {v : Nat} (h : x.toNat = v) :
    x &&& VG.Proof.X25519.Arm.mask16 = BitVec.ofNat 32 (v % 2 ^ 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_ofNat, h]
  omega

/-- Digit `h` of `[a] + [b]`: `x + y + c` to `[r8 + 4h]` and its carry. -/
theorem addDigitD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {P h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (h8 : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 P)
    (hP : P + 4 * h + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 1) :
    WP isa (.block (addDigitD h)) s fun u =>
      u.mem = s.mem.writeW (off base (P + 4 * h)) (BitVec.ofNat 32
        ((hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat = (hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r4, .r5] s u := by
  have hx := hdig_lt (s.gpr .r7).toNat h
  have hy := hdig_lt (s.gpr .r2).toNat h
  simp only [addDigitD]
  refine wp_half hh h6 fun s₁ u₁ => wp_half hh (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have w₅ : Ws s₅ base size :=
    ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  have e8 : s₅.gpr .r8 = s₅.gpr .r12 + BitVec.ofNat 32 P := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h8
  refine wp_str (by omega) (w₅.ea e8 (by omega)) (w₅.write (by omega)) fun s₆ m₆ =>
    wp_mov (op2_lsr (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have v4 : (s₄.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal]
    refine toNat_add_eq (toNat_add_eq (toNat_ofNat_dig _ _) (toNat_ofNat_dig _ _) ?_) rfl ?_ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.mem, m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    simp only [u₅.get, ↓reduceIte, dpVal]
    rw [u₄.other .r6 (by decide), u₃.other .r6 (by decide), u₂.other .r6 (by decide), u₁.other .r6 (by decide), h6]
    exact and_mask_ofNat v4
  · rw [u₇.gpr, toNat_shr, m₆.gpr, u₅.other .r4 (by decide), v4]
  · exact ((((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      (u₅.rest (by simp))).trans ((m₆.rest _).trans (u₇.rest (by simp)))

end VG.Proof.Mont.Arm.Dyn
