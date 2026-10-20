module

public import VerifiedGarbage.Impl.Rsa.Arm.ShiftRight
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A runtime-length in-place one-bit right shift

`shiftRight_ok`: `n` words at `base + o` become the `n + 1` words there
halved (`ShiftRightInv.result`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm

theorem shiftRight_word (x y : BitVec 32) :
    ((x >>> 1) + (y <<< 31)).toNat = x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem shiftRightStep_ok (s : State) (a a' : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (ha' : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = a')
    (wa : InRegions s.wr a 4) (ra : InRegions (s.rd ++ s.wr) a 4)
    (ra' : InRegions (s.rd ++ s.wr) a' 4) :
    WP isa (.block shiftRightStep) s fun t =>
      (t.gpr .r3).toNat = (s.mem.readW a 32).toNat / 2 + 2 ^ 31 * ((s.mem.readW a' 32).toNat % 2) ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r3, .r4, .lr] s t := by
  unfold shiftRightStep
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_ldr (a := a') (by decide) (by rw [u1.other .r0 (by decide), ha'])
    (by rw [u1.rd, u1.wr]; exact ra') fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  have p0 : s4.gpr .r0 = s.gpr .r0 := by
    rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide),
      u1.other .r0 (by decide)]
  refine wp_str (a := a) (by decide) (by rw [p0]; exact ha)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact wa) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 hz => WP.block_nil ?_
  have value : t.gpr .r3 = (s.mem.readW a 32 >>> 1) + (s.mem.readW a' 32 <<< 31) := by
    rw [u7.other .r3 (by decide), u6.other .r3 (by decide), u5.gpr, u4.gpr, dpVal, u3.gpr,
      u3.other .r4 (by decide), u2.gpr, u2.other .r3 (by decide), u1.gpr, u1.mem]
  have count : s5.gpr .lr = s.gpr .lr := by
    rw [u5.gpr, u4.other .lr (by decide), u3.other .lr (by decide), u2.other .lr (by decide),
      u1.other .lr (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value]; exact shiftRight_word _ _
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u7.other .r3 (by decide),
      u6.other .r3 (by decide), u5.gpr]
  · rw [u7.other .r0 (by decide), u6.gpr, dpVal, u5.gpr, p0]
  · rw [u7.gpr, u6.other .lr (by decide), count]
  · rw [hz, u6.other .lr (by decide), count]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest _).trans
        ((u6.rest (by simp)).trans (u7.rest (by simp)))))))

structure ShiftRightCtx (s : State) (base : BitVec 32) (size o n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  fits : o + 4 * (n + 1) ≤ size
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

structure ShiftRightInv (s0 : State) (base : BitVec 32) (o n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : 2 * val32 s.mem (State.addr base) o i + w32 s0.mem (State.addr base) o % 2 =
    val32 s0.mem (State.addr base) o i + 2 ^ (32 * i) * (w32 s0.mem (State.addr base) (o + 4 * i) % 2)
  rest : Rest [.r0, .r3, .r4, .lr] s0 s

theorem shiftRightBody_ok {s0 s : State} {base : BitVec 32} {size o n i : Nat}
    (ctx : ShiftRightCtx s0 base size o n) (inv : ShiftRightInv s0 base o n i s) (hi : i < n) :
    WP isa (.block shiftRightStep) s fun t => ShiftRightInv s0 base o n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have hf := ctx.fits
  have writable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega)⟩
  have readable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable d hd
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have ahi : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr base) (o + 4 * (i + 1)) := by
    rw [inv.ptr, Offset.add_add, show o + 4 * i + 4 = o + 4 * (i + 1) by omega]
    exact VG.Arm.addr_add (by omega)
  refine WP.mono (shiftRightStep_ok s _ _ alo ahi (writable _ (by omega)) (readable _ (by omega))
    (readable _ (by omega))) ?_
  rintro t ⟨value, mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega)
  rw [← mem] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have src := inv.outside.w32 (d := o + 4 * i) (by omega) (by omega)
  have src' := inv.outside.w32 (d := o + 4 * (i + 1)) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [mem, w32_write_self]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega))
  · change (t.gpr .r3).toNat = w32 s.mem (State.addr base) (o + 4 * i) / 2 +
      2 ^ 31 * (w32 s.mem (State.addr base) (o + 4 * (i + 1)) % 2) at value
    rw [src, src'] at value
    rw [val32_succ, val32_succ, low, top, value, pow32_succ]
    have prior := inv.value
    have hx := (s0.mem.readW (off (State.addr base) (o + 4 * i)) 32).isLt
    change 2 * val32 s.mem (State.addr base) o i + w32 s0.mem (State.addr base) o % 2 =
      val32 s0.mem (State.addr base) o i + 2 ^ (32 * i) * (w32 s0.mem (State.addr base) (o + 4 * i) % 2)
      at prior
    generalize w32 s0.mem (State.addr base) (o + 4 * i) = x at *
    generalize w32 s0.mem (State.addr base) (o + 4 * (i + 1)) = y at *
    generalize 2 ^ (32 * i) = P at *
    have hx : P * x = 2 * (P * (x / 2)) + P * (x % 2) := by
      have := Nat.div_add_mod x 2
      calc P * x = P * (2 * (x / 2) + x % 2) := by rw [this]
        _ = _ := by rw [Nat.mul_add, Nat.mul_left_comm]
    have hv : P * (x / 2 + 2 ^ 31 * (y % 2)) = P * (x / 2) + 2 ^ 31 * (P * (y % 2)) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    rw [hx, hv, Nat.mul_assoc]
    generalize P * (y % 2) = C at *
    generalize P * (x / 2) = A at *
    generalize P * (x % 2) = Bm at *
    omega
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem shiftRight_ok (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ShiftRightCtx s base size o n) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o) (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa shiftRight s (ShiftRightInv s base o n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ShiftRightInv s base o n i t
  unfold shiftRight
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (shiftRightBody_ok ctx hi (by omega)) ?_
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
    refine ⟨by omega, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp
    · simpa only [Nat.sub_zero] using hc
    · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]

/-- The halved value, for an incoming word of 0 or 1. -/
theorem ShiftRightInv.result {s t : State} {base : BitVec 32} {o n : Nat}
    (h : ShiftRightInv s base o n n t) (hn : 0 < n)
    (top : w32 s.mem (State.addr base) (o + 4 * n) ≤ 1) :
    val32 t.mem (State.addr base) o n =
      (val32 s.mem (State.addr base) o n + 2 ^ (32 * n) * w32 s.mem (State.addr base) (o + 4 * n)) / 2 := by
  have v := h.value
  have low : val32 s.mem (State.addr base) o n % 2 = w32 s.mem (State.addr base) o % 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [val32]
    omega
  have even : 2 ^ (32 * n) % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.pow_mod]; simp
  rw [Nat.mod_eq_of_lt (by omega : w32 s.mem (State.addr base) (o + 4 * n) < 2)] at v
  have : (2 ^ (32 * n) * w32 s.mem (State.addr base) (o + 4 * n)) % 2 = 0 := by
    rw [Nat.mul_mod, even, Nat.zero_mul]
  omega

end VG.Proof.Rsa.Arm
