module

public import VerifiedGarbage.Impl.Bignum.Arm.ShiftK
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Bignum.Arm.ShiftK
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # In-place shifts by `k` bits on ARMv7

`shiftRightK_ok`: `n` words at `base + o` become the `n + 1` words there shifted right by `k`
(`ShiftRightKInv.result`); `shiftLeftK_ok`: `n` words become `2^k` times them plus `r11`, the bits
shifted out in `r11` (`ShiftLeftKInv.result`), for `0 < k < 32`. Both take `ShiftLeftCtx`'s pointers
(over `n + 1` words for the right shift). `shiftRightK_ct`, `shiftLeftK_ct`: their addresses and
branches depend only on `r0` and `lr`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_lsl op2_lsr dpVal)

theorem two_pow_split {k : Nat} (hk : k < 32) : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hk)]

theorem shiftRightK_word {k : Nat} (hk : k < 32) (x y : BitVec 32) :
    ((x >>> k) + (y <<< (32 - k))).toNat = x.toNat / 2 ^ k + 2 ^ (32 - k) * (y.toNat % 2 ^ k) := by
  have e := two_pow_split hk
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [e, Nat.mul_mod_mul_right, Nat.mul_comm (y.toNat % 2 ^ k)]
  have hx : x.toNat < 2 ^ k * 2 ^ (32 - k) := e ▸ x.isLt
  have h1 : x.toNat / 2 ^ k < 2 ^ (32 - k) := Nat.div_lt_of_lt_mul hx
  have h3 : 2 ^ (32 - k) * (y.toNat % 2 ^ k) + 2 ^ (32 - k) ≤ 2 ^ k * 2 ^ (32 - k) := by
    rw [Nat.mul_comm (2 ^ k), ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact Nat.mod_eq_of_lt (by omega)

theorem shiftLeftK_word {k : Nat} (hk : k < 32) (x c : BitVec 32) (hc : c.toNat < 2 ^ k) :
    (c + (x <<< k)).toNat + 2 ^ 32 * (x >>> (32 - k)).toNat = 2 ^ k * x.toNat + c.toNat := by
  have e : 2 ^ 32 = 2 ^ (32 - k) * 2 ^ k := by rw [two_pow_split hk, Nat.mul_comm]
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [e, Nat.mul_mod_mul_right]
  have h3 : x.toNat % 2 ^ (32 - k) * 2 ^ k + 2 ^ k ≤ 2 ^ (32 - k) * 2 ^ k := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.mod_eq_of_lt (by omega)]
  have d := Nat.div_add_mod x.toNat (2 ^ (32 - k))
  generalize x.toNat / 2 ^ (32 - k) = q at *
  generalize x.toNat % 2 ^ (32 - k) = r at *
  generalize 2 ^ (32 - k) = M at *
  generalize 2 ^ k = K at *
  rw [← d]
  grind

theorem shiftRightKStep_ok {k : Nat} (hk : 0 < k ∧ k < 32) (s : State) (a a' : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (ha' : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = a')
    (wa : InRegions s.wr a 4) (ra : InRegions (s.rd ++ s.wr) a 4)
    (ra' : InRegions (s.rd ++ s.wr) a' 4) :
    WP isa (.block (shiftRightKStep k)) s fun t =>
      (t.gpr .r3).toNat = (s.mem.readW a 32).toNat / 2 ^ k + 2 ^ (32 - k) * ((s.mem.readW a' 32).toNat % 2 ^ k) ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r3, .r4, .lr] s t := by
  unfold shiftRightKStep
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_ldr (a := a') (by decide) (by rw [u1.other .r0 (by decide), ha'])
    (by rw [u1.rd, u1.wr]; exact ra') fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by omega)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by omega)) fun s4 u4 => ?_
  have p0 : s4.gpr .r0 = s.gpr .r0 := by
    rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide),
      u1.other .r0 (by decide)]
  refine wp_str (a := a) (by decide) (by rw [p0]; exact ha)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact wa) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 hz => WP.block_nil ?_
  have value : t.gpr .r3 = (s.mem.readW a 32 >>> k) + (s.mem.readW a' 32 <<< (32 - k)) := by
    rw [u7.other .r3 (by decide), u6.other .r3 (by decide), u5.gpr, u4.gpr, dpVal, u3.gpr,
      u3.other .r4 (by decide), u2.gpr, u2.other .r3 (by decide), u1.gpr, u1.mem]
  have count : s5.gpr .lr = s.gpr .lr := by
    rw [u5.gpr, u4.other .lr (by decide), u3.other .lr (by decide), u2.other .lr (by decide),
      u1.other .lr (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value]; exact shiftRightK_word hk.2 _ _
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u7.other .r3 (by decide),
      u6.other .r3 (by decide), u5.gpr]
  · rw [u7.other .r0 (by decide), u6.gpr, dpVal, u5.gpr, p0]
  · rw [u7.gpr, u6.other .lr (by decide), count]
  · rw [hz, u6.other .lr (by decide), count]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest _).trans
        ((u6.rest (by simp)).trans (u7.rest (by simp)))))))

theorem shiftLeftKStep_ok {k : Nat} (hk : 0 < k ∧ k < 32) (s : State) (a : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (wa : InRegions s.wr a 4) (ra : InRegions (s.rd ++ s.wr) a 4)
    (hc : (s.gpr .r11).toNat < 2 ^ k) :
    WP isa (.block (shiftLeftKStep k)) s fun t =>
      (t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r11).toNat =
        2 ^ k * (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      (t.gpr .r11).toNat < 2 ^ k ∧ t.mem = s.mem.writeW a (t.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r3, .r4, .r11, .lr] s t := by
  unfold shiftLeftKStep
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_dp (op2_lsl (by omega)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by omega)) fun s3 u3 => ?_
  have p0 : s3.gpr .r0 = s.gpr .r0 := by
    rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  refine wp_str (a := a) (by decide) (by rw [p0]; exact ha)
    (by rw [u3.wr, u2.wr, u1.wr]; exact wa) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u6 hz => WP.block_nil ?_
  have value : t.gpr .r3 = s.gpr .r11 + (s.mem.readW a 32 <<< k) := by
    rw [u6.other .r3 (by decide), u5.other .r3 (by decide), u4.gpr,
      u3.other .r3 (by decide), u2.gpr, dpVal, u1.other .r11 (by decide), u1.gpr]
  have carry : t.gpr .r11 = s.mem.readW a 32 >>> (32 - k) := by
    rw [u6.other .r11 (by decide), u5.other .r11 (by decide), u4.gpr, u3.gpr,
      u2.other .r4 (by decide), u1.gpr]
  have count : s4.gpr .lr = s.gpr .lr := by
    rw [u4.gpr, u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value, carry]; exact shiftLeftK_word hk.2 _ _ hc
  · rw [carry, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hx : (s.mem.readW a 32).toNat < 2 ^ (32 - k) * 2 ^ k := by
      rw [Nat.mul_comm, ← two_pow_split hk.2]; exact (s.mem.readW a 32).isLt
    exact Nat.div_lt_of_lt_mul hx
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    rw [u6.other .r3 (by decide), u5.other .r3 (by decide), u4.gpr]
  · rw [u6.other .r0 (by decide), u5.gpr, dpVal, u4.gpr, p0]
  · rw [u6.gpr, u5.other .lr (by decide), count]
  · rw [hz, u5.other .lr (by decide), count]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest _).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))

/-! ## The right shift -/

structure ShiftRightKInv (k : Nat) (s0 : State) (base : BitVec 32) (o n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : 2 ^ k * val32 s.mem (State.addr base) o i + w32 s0.mem (State.addr base) o % 2 ^ k =
    val32 s0.mem (State.addr base) o i + 2 ^ (32 * i) * (w32 s0.mem (State.addr base) (o + 4 * i) % 2 ^ k)
  rest : Rest [.r0, .r3, .r4, .lr] s0 s

theorem shiftRightKBody_ok {k : Nat} (hk : 0 < k ∧ k < 32) {s0 s : State} {base : BitVec 32} {size o n i : Nat}
    (ctx : ShiftLeftCtx s0 base size o (n + 1)) (inv : ShiftRightKInv k s0 base o n i s) (hi : i < n) :
    WP isa (.block (shiftRightKStep k)) s fun t => ShiftRightKInv k s0 base o n (i + 1) t ∧
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
  refine WP.mono (shiftRightKStep_ok hk s _ _ alo ahi (writable _ (by omega)) (readable _ (by omega))
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
  · change (t.gpr .r3).toNat = w32 s.mem (State.addr base) (o + 4 * i) / 2 ^ k +
      2 ^ (32 - k) * (w32 s.mem (State.addr base) (o + 4 * (i + 1)) % 2 ^ k) at value
    rw [src, src'] at value
    rw [val32_succ, val32_succ, low, top, value, pow32_succ, two_pow_split hk.2]
    have prior := inv.value
    have dm := Nat.div_add_mod (w32 s0.mem (State.addr base) (o + 4 * i)) (2 ^ k)
    generalize w32 s0.mem (State.addr base) (o + 4 * i) = x at *
    generalize w32 s0.mem (State.addr base) (o + 4 * (i + 1)) % 2 ^ k = y at *
    generalize x / 2 ^ k = q at *
    generalize x % 2 ^ k = r at *
    generalize 2 ^ (32 * i) = P at *
    generalize 2 ^ (32 - k) = M at *
    generalize 2 ^ k = K at *
    subst dm
    grind
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem shiftRightK_ok {k : Nat} (hk : 0 < k ∧ k < 32) (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ShiftLeftCtx s base size o (n + 1)) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o) (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (shiftRightK k) s (ShiftRightKInv k s base o n n) := by
  let inv := fun j t => ∃ i, i + j = n ∧ 0 < j ∧ ShiftRightKInv k s base o n i t
  unfold shiftRightK
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro j t h
    obtain ⟨i, hij, hj, hi⟩ := h
    refine WP.mono (shiftRightKBody_ok hk ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, j - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp
    · simpa only [Nat.sub_zero] using hc
    · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]

/-- The shifted value: the low `k` bits of the word above come in at the top. -/
theorem ShiftRightKInv.result {k : Nat} (hk : 0 < k ∧ k < 32) {s t : State} {base : BitVec 32} {o n : Nat}
    (h : ShiftRightKInv k s base o n n t) (hn : 0 < n) :
    val32 t.mem (State.addr base) o n =
      (val32 s.mem (State.addr base) o n + 2 ^ (32 * n) * (w32 s.mem (State.addr base) (o + 4 * n) % 2 ^ k)) /
        2 ^ k := by
  have v := h.value
  have low : val32 s.mem (State.addr base) o n % 2 ^ k = w32 s.mem (State.addr base) o % 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [val32, two_pow_split hk.2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  have hK := Nat.two_pow_pos k
  rw [← v, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
    Nat.div_eq_of_lt (Nat.mod_lt _ hK), Nat.zero_add]

/-! ## The left shift -/

structure ShiftLeftKInv (k : Nat) (s0 : State) (base : BitVec 32) (o n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  carry : (s.gpr .r11).toNat < 2 ^ k
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    2 ^ k * val32 s0.mem (State.addr base) o i + (s0.gpr .r11).toNat
  rest : Rest [.r0, .r3, .r4, .r11, .lr] s0 s

theorem shiftLeftKBody_ok {k : Nat} (hk : 0 < k ∧ k < 32) {s0 s : State} {base : BitVec 32} {size o n i : Nat}
    (ctx : ShiftLeftCtx s0 base size o n) (inv : ShiftLeftKInv k s0 base o n i s) (hi : i < n) :
    WP isa (.block (shiftLeftKStep k)) s fun t => ShiftLeftKInv k s0 base o n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have hf := ctx.fits
  have writable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega)⟩
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have read : InRegions (s.rd ++ s.wr) (off (State.addr base) (o + 4 * i)) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable (o + 4 * i) (by omega)
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  refine WP.mono (shiftLeftKStep_ok hk s _ alo (writable _ (by omega)) read inv.carry) ?_
  rintro t ⟨value, carry, mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega)
  rw [← mem] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have source := inv.outside.w32 (d := o + 4 * i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
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
      2 ^ k * w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat at value
    rw [source] at value
    rw [val32_succ, val32_succ, low, top, pow32_succ]
    have prior := inv.value
    generalize 2 ^ (32 * i) = P at *
    generalize 2 ^ k = K at *
    grind
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem shiftLeftK_ok {k : Nat} (hk : 0 < k ∧ k < 32) (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ShiftLeftCtx s base size o n) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hc : s.gpr .lr = BitVec.ofNat 32 n) (carry : (s.gpr .r11).toNat < 2 ^ k) :
    WP isa (shiftLeftK k) s (ShiftLeftKInv k s base o n n) := by
  let inv := fun j t => ∃ i, i + j = n ∧ 0 < j ∧ ShiftLeftKInv k s base o n i t
  unfold shiftLeftK
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro j t h
    obtain ⟨i, hij, hj, hi⟩ := h
    refine WP.mono (shiftLeftKBody_ok hk ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, j - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, carry, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp
    · simpa only [Nat.sub_zero] using hc
    · simp only [val32, Nat.pow_zero, Nat.mul_zero, Nat.one_mul, Nat.zero_add]

/-- The shifted value and the bits shifted out. -/
theorem ShiftLeftKInv.result {k : Nat} {s t : State} {base : BitVec 32} {o n : Nat}
    (h : ShiftLeftKInv k s base o n n t) :
    val32 t.mem (State.addr base) o n =
      (2 ^ k * val32 s.mem (State.addr base) o n + (s.gpr .r11).toNat) % 2 ^ (32 * n) ∧
    (t.gpr .r11).toNat =
      (2 ^ k * val32 s.mem (State.addr base) o n + (s.gpr .r11).toNat) / 2 ^ (32 * n) := by
  rw [← h.value]
  have bound := val32_lt t.mem (State.addr base) o n
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt bound, Nat.zero_add]

/-! ## Constant time -/

/-- `shiftRightK k`'s addresses and branches depend only on `r0` and `lr`, for the `k` the code uses. -/
theorem shiftRightK_ct {k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16) :
    ConstantTime isa (fun _ => True) (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr)
      (shiftRightK k) := by
  have agree : ∀ s t : State, True → True → s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr →
      taint.Agree (Taint.ofRegs [.r0, .lr]) s t := fun _ _ _ _ ⟨h0, hl⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h0
      · exact hl
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .lr]) agree (by taint_decide)

/-- `shiftLeftK k`'s addresses and branches depend only on `r0` and `lr`, for the `k` the code uses. -/
theorem shiftLeftK_ct {k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16) :
    ConstantTime isa (fun _ => True) (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr)
      (shiftLeftK k) := by
  have agree : ∀ s t : State, True → True → s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr →
      taint.Agree (Taint.ofRegs [.r0, .lr]) s t := fun _ _ _ _ ⟨h0, hl⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h0
      · exact hl
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .lr]) agree (by taint_decide)

end VG.Proof.Bignum.Arm
