module

import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A runtime-length in-place one-bit left shift -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure ShiftLeftCtx (s : State) (base : BitVec 32) (size o n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  fits : o + 4 * n ≤ size
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

structure ShiftLeftInv (s0 : State) (base : BitVec 32) (o n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  carry : (s.gpr .r11).toNat ≤ 1
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    2 * val32 s0.mem (State.addr base) o i + (s0.gpr .r11).toNat
  rest : Rest [.r0, .r3, .r4, .r11, .lr] s0 s

theorem shiftLeftBody_ok {s0 s : State} {base : BitVec 32} {size o n i : Nat}
    (ctx : ShiftLeftCtx s0 base size o n) (inv : ShiftLeftInv s0 base o n i s) (hi : i < n) :
    WP isa (.block shiftLeftStep) s fun t => ShiftLeftInv s0 base o n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have hf := ctx.fits
  have writable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega)⟩
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
      off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have read : InRegions (s.rd ++ s.wr) (off (State.addr base) (o + 4 * i)) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable (o + 4 * i) (by omega)
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  refine WP.mono (shiftLeftStep_ok s _ alo (writable _ (by omega)) read inv.carry) ?_
  rintro t ⟨value, carry, mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i)
    (t.gpr .r3) (by omega)
  rw [← mem] at wr
  have low :=  wr.val32 (d := o) (k := i) (by omega) (by omega)
  have source := inv.outside.w32 (d := o + 4 * i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) =
      (t.gpr .r3).toNat := by
    rw [mem, w32_write_self]
  refine ⟨⟨by omega, ?_, ?_, carry, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega))
  · change (t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r11).toNat =
      2 * w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat at value
    rw [source] at value
    rw [val32_succ, val32_succ, low, top, pow32_succ]
    have prior := inv.value
    generalize 2 ^ (32 * i) = P at *
    grind
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

/-- Shift a nonempty range left by one bit in place. Each source word is read before any
store can change it, even though the source and destination overlap. -/
theorem shiftLeft_ok (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ShiftLeftCtx s base size o n) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hc : s.gpr .lr = BitVec.ofNat 32 n) (carry : (s.gpr .r11).toNat ≤ 1) :
    WP isa shiftLeft s (ShiftLeftInv s base o n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ShiftLeftInv s base o n i t
  unfold shiftLeft
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (shiftLeftBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, carry, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp
    · simpa only [Nat.sub_zero] using hc
    · simp only [val32, Nat.pow_zero, Nat.mul_zero, Nat.one_mul, Nat.zero_add]

/-- The exact stored value and carry, without any no-overflow hypothesis. -/
theorem ShiftLeftInv.result {s t : State} {base : BitVec 32} {o n : Nat}
    (h : ShiftLeftInv s base o n n t) :
    val32 t.mem (State.addr base) o n =
      (2 * val32 s.mem (State.addr base) o n + (s.gpr .r11).toNat) % 2 ^ (32 * n) ∧
    (t.gpr .r11).toNat =
      (2 * val32 s.mem (State.addr base) o n + (s.gpr .r11).toNat) / 2 ^ (32 * n) := by
  rw [← h.value]
  have bound := val32_lt t.mem (State.addr base) o n
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt bound, Nat.zero_add]

end VG.Proof.Bignum.Arm
