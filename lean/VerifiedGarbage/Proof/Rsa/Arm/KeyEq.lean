module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Basic.IsEmpty.Defs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Equality of two arrays of the working space, as a slot -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The borrow of a subtraction: whether `a < b`. -/
alias borrow_iff := VG.Proof.Rsa.borrow_iff

theorem eqS_ok {s : State} {B : BitVec 32} {Z w N d a b t : Nat} (h : Ws s B Z w N)
    (ht : t < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hta : t ≠ a) (htb : t ≠ b)
    (hd : d + 4 ≤ hdr) :
    WP isa (eqS d a b t) s fun u => Ws u B Z w N ∧ Keep B w [t] [sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Rest opRegs s u := by
  have hT : sT + 4 ≤ hdr := by decide
  rw [eqS, WP.seq_iff]
  refine WP.mono (sub3_ok h ht ha hb hN hta htb) fun u1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine wp_strSlot h1 hT fun u2 m2 => WP.block_nil ?_
  have h2 := h1.of_mupd m2
  have k2 : Keep B w [] [sT] u1.mem u2.mem := by
    rw [m2.mem]; exact keep_write _ _ (by simp) (by decide)
  have s2 : slot u2.mem B sT = (u1.gpr .r11).toNat := by rw [m2.mem, slot_write_self]
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok h2 ht hb ha hN htb hta) fun u3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  refine wp_ldrSlot h3 hT fun s4 u4 => ?_
  have h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have h5 := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  have h6 := h5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_strSlot h6 hd fun u m7 => WP.block_nil ?_
  have k7 : Keep B w [] [d] u3.mem u.mem := by
    rw [m7.mem, u6.mem, u5.mem, u4.mem]; exact keep_write _ _ (by simp) (by simp only [hdr] at hd; omega)
  have fa := h.fit64 ha
  have fb := h.fit64 hb
  have na2 : num u2.mem B w a = num s.mem B w a := by
    rw [k2.num (by simp) (by simp; decide) fa, k1.num (by simpa using hta) (by simp) fa]
  have nb2 : num u2.mem B w b = num s.mem B w b := by
    rw [k2.num (by simp) (by simp; decide) fb, k1.num (by simpa using htb) (by simp) fb]
  rw [na2, nb2] at v3
  have sT3 : slot u3.mem B sT = (u1.gpr .r11).toNat := by
    rw [k3.slot hT (by simp), s2]
  refine ⟨h6.of_mupd m7, ((k1.join k2 (js := [t]) (ds := [sT, d]))).join (k3.join k7 (js := [t]) (ds := [sT, d]))
      (js := [t]) (ds := [sT, d]), ?_, ?_⟩
  · rw [m7.mem, slot_write_self, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr, u4.other .r11 (by decide)]
    change (((u3.mem.readW (off (State.addr B) sT) 32) ||| u3.gpr .r11) ^^^ 1).toNat = _
    have e : (u3.mem.readW (off (State.addr B) sT) 32).toNat = (u1.gpr .r11).toNat := sT3
    rw [bv_nor_bits (by rw [e]; exact b1) b3, e]
    have p1 := borrow_iff v1 (val32_lt _ _ _ _) b1
    have p3 := borrow_iff v3 (val32_lt _ _ _ _) b3
    by_cases e1 : num s.mem B w a = num s.mem B w b
    · have c1 := p1.mpr (by omega)
      have c3 := p3.mpr (by omega)
      simp [c1, c3, e1]
    · have c : ¬((u1.gpr .r11).toNat = 0 ∧ (u3.gpr .r11).toNat = 0) :=
        fun hh => e1 (by have := p1.mp hh.1; have := p3.mp hh.2; omega)
      simp only [c, e1, ↓reduceIte]
  · exact r1.trans ((m2.rest _).trans (r3.trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
      ((u6.rest (by simp)).trans (m7.rest _))))))

end VG.Proof.Rsa.Arm.Keys
