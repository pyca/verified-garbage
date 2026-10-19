module

public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # Append the quotient bit without a branch on the borrow -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

theorem xorOne_nat (b : BitVec 32) (hb : b.toNat ≤ 1) : (b ^^^ 1).toNat = 1 - b.toNat := by
  have cases : b = 0 ∨ b = 1 := by
    have : b.toNat = 0 ∨ b.toNat = 1 := by omega
    rcases this with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases cases with rfl | rfl <;> decide

theorem quotientBit_raw {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.block quotientBit) s fun t =>
      t.mem = s.mem.writeW (off (State.addr g.base) (g.offsets 0))
        (s.mem.readW (off (State.addr g.base) (g.offsets 0)) 32 + (s.gpr .r11 ^^^ 1)) ∧
      t.gpr .r6 = s.gpr .r6 - 1 ∧ t.z = (s.gpr .r6 - 1 == 0) ∧
      Rest [.r0, .r3, .r6, .r11] s t := by
  unfold quotientBit
  refine h.loadPtr 0 (by decide) fun s1 u1 h1 => ?_
  have fits : g.offsets 0 + 4 ≤ g.size := by
    have f : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
    have := h.positive; omega
  have addr : State.addr (s1.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr g.base) (g.offsets 0) := by
    rw [u1.gpr, BitVec.add_zero]
    exact VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  refine wp_ldr (by decide) addr (h1.workspace.read fits) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_str (a := off (State.addr g.base) (g.offsets 0)) (by decide)
    (by rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide)]; exact addr)
    (by rw [u4.wr, u3.wr, u2.wr]; exact h1.workspace.write fits) fun s5 u5 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u6 hz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
      u4.gpr, dpVal, u3.other .r3 (by decide), u2.gpr, u1.mem,
      u3.gpr, dpVal, u2.other .r11 (by decide), u1.other .r11 (by decide)]
  · rw [u6.gpr, u5.gpr, u4.other .r6 (by decide), u3.other .r6 (by decide),
      u2.other .r6 (by decide), u1.other .r6 (by decide)]
  · rw [hz, u5.gpr, u4.other .r6 (by decide), u3.other .r6 (by decide),
      u2.other .r6 (by decide), u1.other .r6 (by decide)]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest _).trans (u6.rest (by simp))))))

theorem quotientBit_ok {g : Geometry} {s : State} (h : Context g s)
    (borrow : (s.gpr .r11).toNat ≤ 1) :
    WP isa (.block quotientBit) s fun t =>
      (g.value s.mem 0 % 2 = 0 → g.value t.mem 0 = g.value s.mem 0 + 1 - (s.gpr .r11).toNat) ∧
      t.gpr .r6 = s.gpr .r6 - 1 ∧ t.z = (s.gpr .r6 - 1 == 0) ∧ Context g t ∧
      Outside (State.addr g.base) (g.offsets 0) (4 * g.n) s.mem t.mem ∧
      Rest (.r6 :: clobbers) s t := by
  refine WP.mono (quotientBit_raw h) ?_
  rintro t ⟨mem, count, zero, rest⟩
  have fits : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have nowrap := h.workspace.nowrap
  have positive := h.positive
  have outside := writeW32_outside s.mem (State.addr g.base) (d := g.offsets 0)
    (s.mem.readW (off (State.addr g.base) (g.offsets 0)) 32 + (s.gpr .r11 ^^^ 1)) (by omega)
  rw [← mem] at outside
  have frame : Outside (State.addr g.base) (g.offsets 0) (4 * g.n) s.mem t.mem :=
    outside.mono (Nat.le_refl _) (by omega)
  refine ⟨?_, count, zero,
    h.after (Outs.of_outside frame (by simp [Geometry.ranges])) rest.wr (rest.gpr .r8 (by simp)),
    frame, rest.mono (by simp [clobbers])⟩
  intro even
  have low (m : Mem) : g.value m 0 = w32 m (State.addr g.base) (g.offsets 0) +
      2 ^ 32 * val32 m (State.addr g.base) (g.offsets 0 + 4) (g.n - 1) := by
    change val32 _ _ _ g.n = _
    conv => lhs; rw [show g.n = (g.n - 1) + 1 by omega]
    rfl
  rw [low s.mem] at even
  simp only [w32] at even
  have lowEven : (s.mem.readW (off (State.addr g.base) (g.offsets 0)) 32).toNat % 2 = 0 := by omega
  have wordBound := (s.mem.readW (off (State.addr g.base) (g.offsets 0)) 32).isLt
  have high := outside.val32 (d := g.offsets 0 + 4) (k := g.n - 1) (by omega) (by omega)
  rw [low t.mem, low s.mem, high]
  have top : w32 t.mem (State.addr g.base) (g.offsets 0) =
      w32 s.mem (State.addr g.base) (g.offsets 0) + (1 - (s.gpr .r11).toNat) := by
    rw [mem, w32_write_self, BitVec.toNat_add, xorOne_nat _ borrow, Nat.mod_eq_of_lt (by omega)]
  rw [top]
  omega

end VG.Proof.Rsa.Arm.Div
