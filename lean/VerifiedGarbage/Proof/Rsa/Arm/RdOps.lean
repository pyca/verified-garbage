module

-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.Sub32
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Impl.Bignum.Arm.ShiftK
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.ShiftK
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.Arm.ShiftK`, which this module and modules that import it used -/

section

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
  exact Nat.mod_eq_of_lt (by omega_using [h1, h3])

theorem shiftLeftK_word {k : Nat} (hk : k < 32) (x c : BitVec 32) (hc : c.toNat < 2 ^ k) :
    (c + (x <<< k)).toNat + 2 ^ 32 * (x >>> (32 - k)).toNat = 2 ^ k * x.toNat + c.toNat := by
  have e : 2 ^ 32 = 2 ^ (32 - k) * 2 ^ k := by rw [two_pow_split hk, Nat.mul_comm]
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [e, Nat.mul_mod_mul_right]
  have h3 : x.toNat % 2 ^ (32 - k) * 2 ^ k + 2 ^ k ≤ 2 ^ (32 - k) * 2 ^ k := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.mod_eq_of_lt (by omega_using [hc, h3])]
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
  refine wp_mov (op2_lsr (by omega_using [hk])) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by omega_using [hk])) fun s4 u4 => ?_
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
  refine wp_dp (op2_lsl (by omega_using [hk])) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by omega_using [hk])) fun s3 u3 => ?_
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
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega_using [hn, hd])⟩
  have readable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable d hd
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega_using [hi, hn, hf])
  have ahi : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr base) (o + 4 * (i + 1)) := by
    rw [inv.ptr, Offset.add_add, show o + 4 * i + 4 = o + 4 * (i + 1) by omega_using []]
    exact VG.Arm.addr_add (by omega_using [hi, hn, hf])
  refine WP.mono (shiftRightKStep_ok hk s _ _ alo ahi (writable _ (by omega_using [hi, hf])) (readable _ (by omega_using [hi, hf]))
    (readable _ (by omega_using [hi, hf]))) ?_
  rintro t ⟨value, mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega_using [hi, hn, hf])
  rw [← mem] at wr
  have low := wr.val32 (d := o) (k := i) (by omega_using []) (by omega_using [hi, hn, hf])
  have src := inv.outside.w32 (d := o + 4 * i) (by omega_using []) (by omega_using [hi, hn, hf])
  have src' := inv.outside.w32 (d := o + 4 * (i + 1)) (by omega_using []) (by omega_using [hi, hn, hf])
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [mem, w32_write_self]
  refine ⟨⟨by omega_using [hi], ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · exact (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using []))
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
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by omega_using [hn, hf])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

theorem shiftRightK_ok {k : Nat} (hk : 0 < k ∧ k < 32) (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ShiftLeftCtx s base size o (n + 1)) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o) (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (shiftRightK k) s (ShiftRightKInv k s base o n n) := by
  let inv := fun j t => ∃ i, i + j = n ∧ 0 < j ∧ ShiftRightKInv k s base o n i t
  unfold shiftRightK
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro j t h
    obtain ⟨i, hij, hj, hi⟩ := h
    refine WP.mono (shiftRightKBody_ok hk ctx hi (by omega_using [hij, hj])) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, j - 1, by omega_using [hj], i + 1, by omega_using [hij, hj], by omega_using [hij, hj, he], hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    refine ⟨by omega_using [], ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
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
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega_using [hn]⟩
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
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega_using [hn, hd])⟩
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega_using [hi, hn, hf])
  have read : InRegions (s.rd ++ s.wr) (off (State.addr base) (o + 4 * i)) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable (o + 4 * i) (by omega_using [hi, hf])
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  refine WP.mono (shiftLeftKStep_ok hk s _ alo (writable _ (by omega_using [hi, hf])) read inv.carry) ?_
  rintro t ⟨value, carry, mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega_using [hi, hn, hf])
  rw [← mem] at wr
  have low := wr.val32 (d := o) (k := i) (by omega_using []) (by omega_using [hi, hn, hf])
  have source := inv.outside.w32 (d := o + 4 * i) (by omega_using []) (by omega_using [hi, hn, hf])
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [mem, w32_write_self]
  refine ⟨⟨by omega_using [hi], ?_, ?_, carry, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · exact (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using []))
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
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by omega_using [hn, hf])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

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
    refine WP.mono (shiftLeftKBody_ok hk ctx hi (by omega_using [hij, hj])) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, j - 1, by omega_using [hj], i + 1, by omega_using [hij, hj], by omega_using [hij, hj, he], hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    refine ⟨by omega_using [], ?_, ?_, carry, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
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

end

end

/-! # `vg_rsa_recover_primes_det` on ARMv7: the operations Appendix C.2 adds

On a stage of the key working space (`KS`): the switch between the narrow
and wide arrays from `r9` alone (`toW_ok`, `toN_ok`), a narrow halving
(`KS.half_w`), a shift left by one bit with its carry on either view
(`KS.shl_w`, `KS.shl_W`), the low word of a wide array set to one
(`KS.setOne_W`), and the header words of the checks and the counts.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.Rsa (sub32 b2n)

/-- Evaluates the arrays' and header words' functions of a stage at their
indices: unfolds `upd` and the indices' names, then decides the `if`s. -/
macro "rd_ev" : tactic => `(tactic| (simp only [upd, VG.Impl.Rsa.Arm.RecoverDet.wZ, VG.Impl.Rsa.Arm.RecoverDet.wOne, VG.Impl.Rsa.Arm.RecoverDet.wX,
    VG.Impl.Rsa.Arm.RecoverDet.wX3, VG.Impl.Rsa.Arm.RecoverDet.wT1, VG.Impl.Rsa.Arm.RecoverDet.wT2,
    VG.Impl.Rsa.Arm.RecoverDet.wA, VG.Impl.Rsa.Arm.RecoverDet.wN, VG.Impl.Rsa.Arm.RecoverDet.wR,
    VG.Impl.Rsa.Arm.RecoverDet.wDt, VG.Impl.Rsa.Arm.RecoverDet.wB, VG.Impl.Rsa.Arm.RecoverDet.aN,
    VG.Impl.Rsa.Arm.RecoverDet.aZN, VG.Impl.Rsa.Arm.RecoverDet.aOneN, VG.Impl.Rsa.Arm.RecoverDet.aT1,
    VG.Impl.Rsa.Arm.RecoverDet.aT2, VG.Impl.Rsa.Arm.RecoverDet.aU, VG.Impl.Rsa.Arm.RecoverDet.aX2,
    VG.Impl.Rsa.Arm.RecoverDet.aGx, VG.Impl.Rsa.Arm.RecoverDet.aG1, VG.Impl.Rsa.Arm.RecoverDet.aG,
    VG.Impl.Rsa.Arm.RecoverDet.aMlo, VG.Impl.Rsa.Arm.RecoverDet.aM1, VG.Impl.Rsa.Arm.RecoverDet.aD,
    VG.Impl.Rsa.Arm.RecoverDet.aRlo, VG.Impl.Rsa.Arm.RecoverDet.aRem, VG.Impl.Rsa.Arm.RecoverDet.aDt,
    VG.Impl.Rsa.Arm.RecoverDet.aB, VG.Impl.Rsa.Arm.RecoverDet.aBy,
    VG.Impl.Rsa.Arm.RecoverDet.aY,
    VG.Impl.Rsa.Arm.RecoverDet.aP, VG.Impl.Rsa.Arm.RecoverDet.aQ, VG.Impl.Rsa.Arm.RecoverDet.sB0,
    VG.Impl.Rsa.Arm.RecoverDet.sB1, VG.Impl.Rsa.Arm.RecoverDet.sOkDE,
    VG.Impl.Rsa.Arm.RecoverDet.sY, VG.Impl.Rsa.Arm.RecoverDet.sLt,
    VG.Impl.Rsa.Arm.RecoverDet.sExact, VG.Impl.Rsa.Arm.RecoverDet.sC1,
    VG.Impl.Rsa.Arm.RecoverDet.sC2, VG.Impl.Rsa.Arm.RecoverDet.sOk4,
    VG.Impl.Rsa.Arm.RecoverDet.sOk5, VG.Impl.Rsa.Arm.RecoverDet.sK, VG.Impl.Rsa.Arm.RecoverDet.sU1, VG.Impl.Rsa.Arm.RecoverDet.sM0,
    VG.Impl.Rsa.Arm.RecoverDet.sMask, VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wMod,
    VG.Impl.Rsa.Arm.Recover.wZ, VG.Impl.Rsa.Arm.Recover.wE, VG.Impl.Rsa.Arm.Recover.wD,
    VG.Impl.Rsa.Arm.Recover.aN, VG.Impl.Rsa.Arm.Recover.sMask]; try simp))

/-- Reads the functions of a stage through their updates at literal indices,
leaving the functions under them folded. -/
macro "rd_up" : tactic => `(tactic| simp (disch := decide) only [upd_ne, upd_self])

/-! ## The shift -/

/-- `shlN j` over `n` words (`lr`): `[j]`'s low `n` words := `2 [j] + r11` modulo `2^(32 n)`, the bit
shifted out in `r11`. -/
theorem shlN_ok {s : State} {B : BitVec 32} {Z w N j n : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (carry : (s.gpr .r11).toNat ≤ 1) (hn : 0 < n) (hnw : n ≤ w)
    (hlr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (shlN j) s fun t => Ws t B Z w N ∧ Outside (State.addr B) (arr w j) (4 * n) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr w j) n =
        (2 * val32 s.mem (State.addr B) (arr w j) n + (s.gpr .r11).toNat) % 2 ^ (32 * n) ∧
      (t.gpr .r11).toNat = (2 * val32 s.mem (State.addr B) (arr w j) n + (s.gpr .r11).toNat) / 2 ^ (32 * n) ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  rw [shlN, WP.seq_iff, ← List.append_nil (ptr .r0 j)]
  refine ptr_ok h (r := .r0) (by decide) (j := j) (by omega_using [hj, hN]) (rest := []) fun s1 p1 r1 m1 h1 => WP.block_nil ?_
  have r11 : s1.gpr .r11 = s.gpr .r11 := r1.gpr _ (by decide)
  refine WP.mono (VG.Proof.Bignum.Arm.shiftLeft_ok s1 (base := B) (size := Z) (o := arr w j) (n := n)
    ⟨nw, by omega_using [hnw, fit, hS], h1.writable⟩ hn p1 (by rw [r1.gpr _ (by decide), hlr])
    (by rw [r11]; exact carry)) fun t inv => ?_
  obtain ⟨res, cout⟩ := inv.result
  rw [m1, r11] at res cout
  refine ⟨h1.rest inv.rest, by simpa only [Nat.add_zero, m1] using inv.outside, res, cout,
    (r1.mono (by simp)).trans (inv.rest.mono (by simp))⟩

/-- `shl j`: `[j] := 2 [j] + r11` modulo `2^(32 w)`, the bit shifted out in `r11`. -/
theorem shl_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (carry : (s.gpr .r11).toNat ≤ 1) :
    WP isa (shl j) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (2 * num s.mem B w j + (s.gpr .r11).toNat) % 2 ^ (32 * w) ∧
      (t.gpr .r11).toNat = (2 * num s.mem B w j + (s.gpr .r11).toNat) / 2 ^ (32 * w) ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  rw [shl, WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun u u1 => WP.block_nil ?_
  have hu : Ws u B Z w N := h.of_upd u1 (by decide) (by decide) (by decide)
  have r11 : u.gpr .r11 = s.gpr .r11 := u1.other _ (by decide)
  refine WP.mono (shlN_ok hu hj hN (by rw [r11]; exact carry) h.wpos (Nat.le_refl _) (by rw [u1.gpr, h.r9]))
    fun t ⟨ht, O, v, c, r⟩ => ?_
  rw [u1.mem] at O
  rw [u1.mem, r11] at v c
  refine ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by omega_using [hS]) (by simp), ?_, ?_,
    (u1.rest (by simp)).trans r⟩
  · simp only [num]; exact v
  · simp only [num]; exact c

/-- `halfKN j k`: `[j] := ⌊([j] + r11 · 2^(32 w)) / 2^k⌋`, for `r11 < 2^k`. -/
theorem halfKN_ok {k : Nat} (hk : 0 < k ∧ k < 32) {s : State} {B : BitVec 32} {Z w N j : Nat}
    (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256) (bits : (s.gpr .r11).toNat < 2 ^ k) :
    WP isa (halfKN j k) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .r11).toNat) / 2 ^ k ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  rw [halfKN, WP.seq_iff]
  refine ptr_ok h (by decide) (by omega_using [hj, hN]) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have a2 : State.addr (s2.gpr .r1 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * w) := by
    have e : s2.gpr .r1 = B + BitVec.ofNat 32 (arr w j + 4 * w) := by
      rw [u2.gpr, dpVal, p1]
      have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have := h.wle
        omega_using []
      rw [h1.r9, this, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e, Offset.add_add, Nat.add_zero]
    exact h.addr (by omega_using [fit, hS])
  have h2 : Ws s2 B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_str (by decide) a2 (h2.write (by omega_using [fit, hS])) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_mupd u3
  refine wp_mov (op2_reg _ _) fun u u4 => WP.block_nil ?_
  have hu : Ws u B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * w)) (s.gpr .r11) := by
    rw [u4.mem, u3.mem, u2.mem, m1, u2.other .r11 (by decide), r1.gpr _ (by decide)]
  have restU : Rest opRegs s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest _).trans (u4.rest (by simp))))
  have outS := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * w) (s.gpr .r11) (by omega_using [fit, hS, nw])
  rw [← mu] at outS
  refine WP.mono (VG.Proof.Bignum.Arm.shiftRightK_ok hk u (base := B) (size := Z) (o := arr w j) (n := w)
    ⟨nw, by omega_using [fit, hS], hu.writable⟩ h.wpos
    (by rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), p1])
    (by rw [u4.gpr, h3.r9])) ?_
  intro t inv
  have top : w32 u.mem (State.addr B) (arr w j + 4 * w) = (s.gpr .r11).toNat := by
    rw [mu, w32_write_self]
  have res := inv.result hk h.wpos
  have low := outS.val32 (d := arr w j) (k := w) (by omega_using []) (by omega_using [fit, hS, nw])
  refine ⟨hu.rest inv.rest, (Keep.of_arr (d := 4 * w) outS (by omega_using [hS]) (by simp)).trans
    (Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside) (by omega_using [hS]) (by simp)),
    ?_, restU.trans (inv.rest.mono (by simp))⟩
  change val32 _ _ _ _ = _
  rw [res, low, top, Nat.mod_eq_of_lt bits]

/-- `shlKN j k` over the width: `[j] := 2^k [j] + r11` modulo `2^(32 w)`, the bits shifted out in `r11`. -/
theorem shlKN_ok {k : Nat} (hk : 0 < k ∧ k < 32) {s : State} {B : BitVec 32} {Z w N j : Nat}
    (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256) (bits : (s.gpr .r11).toNat < 2 ^ k) :
    WP isa (shlKN j k) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (2 ^ k * num s.mem B w j + (s.gpr .r11).toNat) % 2 ^ (32 * w) ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  rw [shlKN, WP.seq_iff, ← List.append_nil (ptr .r0 j)]
  refine wp_mov (op2_reg _ _) fun u u1 => ?_
  have hu : Ws u B Z w N := h.of_upd u1 (by decide) (by decide) (by decide)
  refine ptr_ok hu (r := .r0) (by decide) (j := j) (by omega_using [hj, hN]) (rest := []) fun s1 p1 r1 m1 h1 => WP.block_nil ?_
  have r11 : s1.gpr .r11 = s.gpr .r11 := by rw [r1.gpr _ (by decide), u1.other _ (by decide)]
  refine WP.mono (VG.Proof.Bignum.Arm.shiftLeftK_ok hk s1 (base := B) (size := Z) (o := arr w j) (n := w)
    ⟨nw, by omega_using [fit, hS], h1.writable⟩ h.wpos p1 (by rw [r1.gpr _ (by decide), u1.gpr, h.r9])
    (by rw [r11]; exact bits)) fun t inv => ?_
  obtain ⟨res, _⟩ := inv.result
  rw [m1, u1.mem, r11] at res
  refine ⟨h1.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, m1, u1.mem] using inv.outside)
    (by omega_using [hS]) (by simp), res, ((u1.rest (by simp)).trans (r1.mono (by simp))).trans (inv.rest.mono (by simp))⟩

/-- `copy o a`, with the words of `[o]` above its `w` kept. -/
theorem copy_out_ok {s : State} {B : BitVec 32} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Outside (State.addr B) (arr w o) (4 * w) s.mem t.mem ∧
      Rest opRegs s t := by
  rw [copy]
  refine WP.mono (copyN_ok h ho ha hN hoa h.wpos (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩)) fun t ⟨ht, O, v, R⟩ =>
    ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by simp only [S]; omega_using []) (by simp), v, O, R⟩

/-- A number of `W` words: its low `w` words are the narrow array `2 j`'s number. -/
theorem numW_split (m : Mem) (B : BitVec 32) (w j : Nat) :
    num m B (2 * w + 2) j = num m B w (2 * j) +
      2 ^ (32 * w) * (val32 m (State.addr B) (arr w (2 * j) + 4 * w) 2 + 2 ^ 64 * num m B w (2 * j + 1)) := by
  have e : 2 ^ (32 * (w + 2)) = 2 ^ (32 * w) * 2 ^ 64 := by
    rw [← Nat.pow_add, show 32 * (w + 2) = 32 * w + 64 by omega_using []]
  rw [numW, val32_append, e, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem KS.shl_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (carry : (s.gpr .r11).toNat ≤ 1) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (shl j) s fun t =>
      KS P σ (upd A j ((2 * A j + (s.gpr .r11).toNat) % 2 ^ (32 * P.w))) (j :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ (t.gpr .r11).toNat = (2 * A j + (s.gpr .r11).toNat) / 2 ^ (32 * P.w) ∧
      Rest opRegs s t :=
  WP.mono (shl_ok hv (h.live_lt j hj) (by decide) carry) fun _ ⟨ht, k, e, c, r⟩ =>
    ⟨h.write_w k (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrs j hj]) hlW (by simp),
      ht, by rw [c, h.arrs j hj], r⟩

theorem KS.shl_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (carry : (s.gpr .r11).toNat ≤ 1) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (shl j) s fun t =>
      KS P σ A live (upd AW j ((2 * AW j + (s.gpr .r11).toNat) % 2 ^ (32 * P.W))) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ (t.gpr .r11).toNat = (2 * AW j + (s.gpr .r11).toNat) / 2 ^ (32 * P.W) ∧
      Rest opRegs s t :=
  WP.mono (shl_ok hv (h.liveW_lt j hj) (by decide) carry) fun _ ⟨ht, k, e, c, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]) hl (by simp),
      ht, by rw [c, h.arrsW j hj], r⟩

theorem KS.half_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (r11 : (s.gpr .r11).toNat = 0) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (half j) s fun t => KS P σ (upd A j (A j / 2)) (j :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t :=
  WP.mono (Keys.half_ok hv (h.live_lt j hj) (by decide) (by omega_using [r11])) fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_w k (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrs j hj]) hlW (by simp), ht, r⟩

theorem KS.half_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (r11 : (s.gpr .r11).toNat = 0) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (half j) s fun t => KS P σ A live (upd AW j (AW j / 2)) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (Keys.half_ok hv (h.liveW_lt j hj) (by decide) (by omega_using [r11])) fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrsW j hj]) hl (by simp), ht, r⟩

theorem KS.halfK_w {j k : Nat} (hk : 0 < k ∧ k < 32) (h : KS P σ A live AW liveW V ls s)
    (hv : Ws s P.B P.Z P.w nArr) (hj : j ∈ live) (r11 : (s.gpr .r11).toNat = 0) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (halfKN j k) s fun t => KS P σ (upd A j (A j / 2 ^ k)) (j :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t :=
  WP.mono (halfKN_ok hk hv (h.live_lt j hj) (by decide) (by rw [r11]; exact Nat.two_pow_pos _))
    fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_w k (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrs j hj]) hlW (by simp), ht, r⟩

theorem KS.shlK_W {j k : Nat} (hk : 0 < k ∧ k < 32) (h : KS P σ A live AW liveW V ls s)
    (hv : Ws s P.B P.Z P.W 22) (hj : j ∈ liveW) (r11 : (s.gpr .r11).toNat = 0) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (shlKN j k) s fun t =>
      KS P σ A live (upd AW j (AW j * 2 ^ k % 2 ^ (32 * P.W))) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (shlKN_ok hk hv (h.liveW_lt j hj) (by decide) (by rw [r11]; exact Nat.two_pow_pos _))
    fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.add_zero, h.arrsW j hj, Nat.mul_comm]) hl (by simp), ht, r⟩

theorem KS.setOne_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd AW j (1 + 2 ^ 32 * (AW j / 2 ^ 32))) (j :: liveW) V ls t →
      Ws t P.B P.Z P.W 22 → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setOne j ++ rest)) s Q :=
  Keys.setOne_ok hv (h.liveW_lt j hj) (by decide) fun t ht kt e r =>
    k t (h.write_W kt (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]) hl
      (by simp)) ht r

/-- The narrow view of a wide array's low half. -/
theorem KS.narrow {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ liveW) (h2 : 2 * j < nArr) :
    KS P σ (upd A (2 * j) (AW j % 2 ^ (32 * P.w))) (2 * j :: live) AW liveW V ls s := by
  refine ⟨h.bs, h.r8, h.cnt, fun i hi => ?_, h.arrsW, h.sl,
    fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ h2) (h.live_lt i), h.liveW_lt, h.ls_ok⟩
  by_cases e : i = 2 * j
  · subst e
    rw [upd_self, ← h.arrsW j hj]
    change _ = num s.mem P.B (2 * P.w + 2) j % _
    rw [numW_split s.mem P.B P.w j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
  · rw [upd_ne _ _ e]; exact h.arrs i ((List.mem_cons.mp hi).resolve_left e)

/-- `copy (2 j) a` into the low half of a zero wide array `j`: the wide array holds `[a]`. -/
theorem KS.widen {j a : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : 2 * j + 1 < nArr) (z : num s.mem P.B P.W j = 0) (ha : a ∈ live) (h2a : 2 * j ≠ a)
    (hl : ∀ i ∈ live, i ≠ 2 * j) (hlW : ∀ i ∈ liveW, i ≠ j) :
    WP isa (copy (2 * j) a) s fun t =>
      KS P σ A live (upd AW j (A a)) (j :: liveW) V ls t ∧ Ws t P.B P.Z P.w nArr := by
  have sz := h.sizes
  refine WP.mono (copy_out_ok hv (by omega_using [hj]) (h.live_lt a ha) (by decide) h2a) fun t ⟨ht, k, e, out, r⟩ => ⟨?_, ht⟩
  have f2 := fit_w sz (show 2 * j < nArr by omega_using [hj])
  have f2Z := fitZ_w sz (show 2 * j < nArr by omega_using [hj])
  have f3 := fit_w sz hj
  have hS : S P.w = 4 * (P.w + 2) := rfl
  have hi : num t.mem P.B P.w (2 * j + 1) = num s.mem P.B P.w (2 * j + 1) :=
    k.num (by simp) (by simp) f3
  have hx : val32 t.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 =
      val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 := out.val32 (by omega_using []) (by omega_using [f2, hS])
  change num s.mem P.B (2 * P.w + 2) j = 0 at z
  rw [numW_split s.mem P.B P.w j] at z
  have z1 : val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 + 2 ^ 64 * num s.mem P.B P.w (2 * j + 1) = 0 := by
    have p : 0 < 2 ^ (32 * P.w) := Nat.two_pow_pos _
    rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 +
      2 ^ 64 * num s.mem P.B P.w (2 * j + 1)) with c | c
    · exact c
    · have := Nat.mul_pos p c; omega_using [z, this]
  have vt : num t.mem P.B P.W j = A a := by
    change num t.mem P.B (2 * P.w + 2) j = _
    rw [numW_split t.mem P.B P.w j, e, hi, hx, z1, Nat.mul_zero, Nat.add_zero, h.arrs a ha]
  refine h.core k (by simpa using f2Z) (by simp) (h.r8_of r) r.sp r.rd r.wr (h.arrs_w k (fun i hi o ho => by
      simp only [List.mem_singleton] at ho; subst ho; exact Ne.symm (hl i hi)) (by simp)) h.live_lt
    (fun i hi => ?_) (fun i hi => (List.mem_cons.mp hi).elim (fun e => by subst e; have : nArr = 44 := rfl; omega_using [hj, this]) (h.liveW_lt i))
    (h.sl_keep k (by simp)) h.ls_ok
  by_cases e' : i = j
  · subst e'; rw [upd_self, vt]
  · rw [upd_ne _ _ e']
    exact h.arrsW_w k (fun i hi o ho => by
      simp only [List.mem_singleton] at ho; subst ho; have := hlW i hi; omega_using [this]) (by simp) i
      ((List.mem_cons.mp hi).resolve_left e')

/-- A narrow array recorded at the value it holds. -/
theorem KS.addLive {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j < nArr) :
    KS P σ (upd A j (num s.mem P.B P.w j)) (j :: live) AW liveW V ls s := by
  refine ⟨h.bs, h.r8, h.cnt, fun i hi => ?_, h.arrsW, h.sl,
    fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ hj) (h.live_lt i), h.liveW_lt, h.ls_ok⟩
  by_cases e : i = j
  · subst e; rw [upd_self]
  · rw [upd_ne _ _ e]; exact h.arrs i ((List.mem_cons.mp hi).resolve_left e)

/-! ## Values, differences and sums -/

theorem KS.lt_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ live) : A j < 2 ^ (32 * P.w) := by
  rw [← h.arrs j hj]; exact val32_lt _ _ _ _

theorem KS.lt_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ liveW) : AW j < 2 ^ (32 * P.W) := by
  rw [← h.arrsW j hj]; exact val32_lt _ _ _ _

/-- `[o] := [a] - [b]` with `w` words, and its borrow. -/
theorem KS.sub_w {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 o a b) s fun t => KS P σ (upd A o (sub32 P.w (A a) (A b))) (o :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t ∧ (t.gpr .r11).toNat = b2n (decide (A a < A b)) :=
  WP.mono (h.sub3_w hv ho ha hb hoa hob hlW) fun _ ⟨X, ht, hwt, r, e, c⟩ => by
    have hX : X < 2 ^ (32 * P.w) := by
      have := ht.lt_w (List.mem_cons_self ..); rwa [upd_self] at this
    obtain ⟨xv, cv⟩ := sub32_of hX (h.lt_w hb) e c
    subst xv
    exact ⟨ht, hwt, r, cv⟩

/-- `[o] := [a] - [b]` with `W` words, and its borrow. -/
theorem KS.sub_W {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 o a b) s fun t => KS P σ A live (upd AW o (sub32 P.W (AW a) (AW b))) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t ∧ (t.gpr .r11).toNat = b2n (decide (AW a < AW b)) :=
  WP.mono (h.sub3_W hv ho ha hb hoa hob hl) fun _ ⟨X, ht, hwt, r, e, c⟩ => by
    have hX : X < 2 ^ (32 * P.W) := by
      have := ht.lt_W (List.mem_cons_self ..); rwa [upd_self] at this
    obtain ⟨xv, cv⟩ := sub32_of hX (h.lt_W hb) e c
    subst xv
    exact ⟨ht, hwt, r, cv⟩

@[simp] theorem sub32_self (w a : Nat) : sub32 w a a = 0 := by unfold sub32; simp

/-- A sum through a negation. -/
theorem sub32_neg {w a b : Nat} (ha : a < 2 ^ (32 * w)) (hb : b < 2 ^ (32 * w)) :
    sub32 w a (sub32 w 0 b) = (a + b) % 2 ^ (32 * w) := by
  unfold sub32
  rcases Nat.eq_zero_or_pos b with rfl | pos
  · simp [Nat.mod_eq_of_lt ha]
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (a := 2 ^ (32 * w) - b) (by omega_using [ha, pos]),
      show a + 2 ^ (32 * w) - (2 ^ (32 * w) - b) = a + b by omega_using [hb]]

/-- `add o a b t z`: `[o] := [a] + [b]` with `w` words, through `[t] := 0 - [b]`, `[z] = 0`. -/
theorem KS.add_w {o a b t z : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ht : t < nArr) (ha : a ∈ live) (hb : b ∈ live) (hz : z ∈ live) (z0 : A z = 0)
    (hta : t ≠ a) (htb : t ≠ b) (htz : t ≠ z) (hoa : o ≠ a) (hot : o ≠ t)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j ∧ t / 2 ≠ j) :
    WP isa (add o a b t z) s fun u =>
      KS P σ (upd (upd A t (sub32 P.w 0 (A b))) o ((A a + A b) % 2 ^ (32 * P.w))) (o :: t :: live) AW liveW
        V ls u ∧ Ws u P.B P.Z P.w nArr := by
  unfold add
  refine WP.seq (WP.mono (h.sub_w hv ht hz hb htz htb fun j hj => (hlW j hj).2) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  rw [z0] at h1
  refine WP.mono (h1.sub_w hv1 ho (List.mem_cons_of_mem _ ha) (List.mem_cons_self ..) hoa hot
    fun j hj => (hlW j hj).1) fun u ⟨hu, hvu, _, _⟩ => ⟨?_, hvu⟩
  rwa [upd_ne _ _ (Ne.symm hta), upd_self, sub32_neg (h.lt_w ha) (h.lt_w hb)] at hu

/-- `add o a b t z` with `W` words. -/
theorem KS.add_W {o a b t z : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ht : t < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hz : z ∈ liveW) (z0 : AW z = 0)
    (hta : t ≠ a) (htb : t ≠ b) (htz : t ≠ z) (hoa : o ≠ a) (hot : o ≠ t)
    (hl : ∀ j ∈ live, j / 2 ≠ o ∧ j / 2 ≠ t) :
    WP isa (add o a b t z) s fun u =>
      KS P σ A live (upd (upd AW t (sub32 P.W 0 (AW b))) o ((AW a + AW b) % 2 ^ (32 * P.W))) (o :: t :: liveW)
        V ls u ∧ Ws u P.B P.Z P.W 22 := by
  unfold add
  refine WP.seq (WP.mono (h.sub_W hv ht hz hb htz htb fun j hj => (hl j hj).2) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  rw [z0] at h1
  refine WP.mono (h1.sub_W hv1 ho (List.mem_cons_of_mem _ ha) (List.mem_cons_self ..) hoa hot
    fun j hj => (hl j hj).1) fun u ⟨hu, hvu, _, _⟩ => ⟨?_, hvu⟩
  rwa [upd_ne _ _ (Ne.symm hta), upd_self, sub32_neg (h.lt_W ha) (h.lt_W hb)] at hu

/-! ## Header words -/

/-- `brw d`: the header word `d := r11`. -/
theorem KS.brw {d : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (s.gpr .r11).toNat) (d :: ls) t → Ws t P.B P.Z v N →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (brw d ++ rest)) s Q :=
  h.strSlot hv hd fun t ht hvt g _ => k t ht hvt g

/-- `notS d a`: the header word `d :=` the bit `a` negated. -/
theorem KS.notS {d a : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (bit : V a ≤ 1) (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (1 - V a)) (d :: ls) t → Ws t P.B P.Z v N →
      WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.notS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s2.gpr .r1).toNat = 1 - V a := by
    rw [u2.gpr, dpVal, u1.gpr,
      VG.Proof.Rsa.KeyBits32.bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega_using [bit]) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega_using [bit]
  rw [e] at ht; exact ht

/-- `norS d a b`: the header word `d :=` neither of the bits `a` and `b`. -/
theorem KS.norS {d a b : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (hb : b ∈ ls) (bita : V a ≤ 1) (bitb : V b ≤ 1) (hd : SlotOk d)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (if V a = 0 ∧ V b = 0 then 1 else 0)) (d :: ls) t →
      Ws t P.B P.Z v N → WP isa (.block rest) t Q) :
    WP isa (.block (norS d a b ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.norS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine h1.ldrSlot hv1 hb (r := .r2) (by decide) fun s2 h2 hv2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine h4.strSlot hv4 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s4.gpr .r1).toNat = if V a = 0 ∧ V b = 0 then 1 else 0 := by
    rw [u4.gpr, dpVal, u3.gpr, dpVal, u2.other .r1 (by decide), u1.gpr, u2.gpr]
    rw [VG.Proof.Rsa.KeyBits32.bv_nor_bits (by rw [BitVec.toNat_ofNat]; omega_using [bita]) (by rw [BitVec.toNat_ofNat]; omega_using [bitb]),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bita]), Nat.mod_eq_of_lt (by omega_using [bitb])]
  rw [e] at ht; exact ht

/-- `andS d a b`: the header word `d :=` the bits `a` and `b`. -/
theorem KS.andS {d a b : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (hb : b ∈ ls) (bita : V a ≤ 1) (bitb : V b ≤ 1) (hd : SlotOk d)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (if V a = 1 ∧ V b = 1 then 1 else 0)) (d :: ls) t →
      Ws t P.B P.Z v N → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.Keys.andS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine h1.ldrSlot hv1 hb (r := .r2) (by decide) fun s2 h2 hv2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine h3.strSlot hv3 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s3.gpr .r1).toNat = if V a = 1 ∧ V b = 1 then 1 else 0 := by
    rw [u3.gpr, dpVal, u2.other .r1 (by decide), u1.gpr, u2.gpr]
    rw [VG.Proof.Rsa.KeyBits32.bv_and_bits (by rw [BitVec.toNat_ofNat]; omega_using [bita]) (by rw [BitVec.toNat_ofNat]; omega_using [bitb]),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bita]), Nat.mod_eq_of_lt (by omega_using [bitb])]
  rw [e] at ht; exact ht

/-- `mov r11, #0`. -/
theorem KS.clr11 {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z v N → (t.gpr .r11).toNat = 0 →
      WP isa (.block rest) t Q) :
    WP isa (.block (clr11 ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.clr11
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun t u => ?_
  obtain ⟨ht, hvt⟩ := h.reg hv (u.rest (ws := [.r11]) (by simp)) u.mem
  exact k t ht hvt (by rw [u.gpr]; rfl)

/-! ## Counts -/

/-- `cntNext`: the count less one, and Z if it is zero. -/
theorem KS.cntNext {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hc : sK ∈ ls) (h1 : 1 ≤ V sK) (h2 : V sK < 2 ^ 32) :
    WP isa (.block VG.Impl.Rsa.Arm.RecoverDet.cntNext) s fun t =>
      KS P σ A live AW liveW (upd V sK (V sK - 1)) (sK :: ls) t ∧
      Ws t P.B P.Z v N ∧ t.z = decide (V sK - 1 = 0) := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.cntNext
  refine h.ldrSlot hv hc (r := .r1) (by decide) fun s1 h1' hv1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2', hv2⟩ := h1'.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2'.strSlot hv2 (d := sK) (r := .r1) (by decide) fun t ht hvt gt zt => WP.block_nil ⟨?_, hvt, ?_⟩
  · have e : (s2.gpr .r1).toNat = V sK - 1 := by
      rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [h1]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h2])]
    rw [e] at ht; exact ht
  · rw [zt, z2, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [h1])]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [h2])]
    rfl

/-! ## The widths -/

/-- `toW`: from the narrow arrays to the wide ones. -/
theorem KS.toW (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z P.W 22 → Rest [.r9, .r7] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (toW ++ rest)) s Q := by
  have sz := h.sizes
  have wl := sz.wle
  unfold VG.Impl.Rsa.Arm.RecoverDet.toW
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u3.gpr, dpVal, u2.gpr, hv.r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega_using []
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by have := sz.Wle; omega_using [this]) e9 fun t h7 r m => ?_
  have rt : Rest [.r9, .r7] s t := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (r.mono (by simp)))
  have mt : t.mem = s.mem := m.trans (u3.mem.trans u2.mem)
  refine k t (h.of_rest rt mt (by decide)) ⟨hv.nowrap, by rw [rt.wr]; exact hv.writable,
    by rw [arrW_end]; exact sz.fits, by show 0 < 2 * P.w + 2; omega_using [], by have := sz.Wle; omega_using [this], h7,
    by rw [rt.gpr _ (by decide), hv.r8], by rw [r.gpr _ (by decide), e9]⟩ rt

/-- `toN`: from the wide arrays to the narrow ones. -/
theorem KS.toN (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z P.w nArr → Rest [.r9, .r7] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (toN ++ rest)) s Q := by
  have sz := h.sizes
  have wl := sz.wle
  unfold VG.Impl.Rsa.Arm.RecoverDet.toN
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.w := by
    rw [u3.gpr, u2.gpr, dpVal, hv.r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega_using [wl]
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by omega_using [wl]) e9 fun t h7 r m => ?_
  have rt : Rest [.r9, .r7] s t := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (r.mono (by simp)))
  have mt : t.mem = s.mem := m.trans (u3.mem.trans u2.mem)
  refine k t (h.of_rest rt mt (by decide)) ⟨hv.nowrap, by rw [rt.wr]; exact hv.writable,
    sz.fits, by show 0 < 2 * P.w6 + 2; omega_using [], by omega_using [wl], h7,
    by rw [rt.gpr _ (by decide), hv.r8], by rw [r.gpr _ (by decide), e9]⟩ rt

end

end VG.Proof.Rsa.Arm.Recover
