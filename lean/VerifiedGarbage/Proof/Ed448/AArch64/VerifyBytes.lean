module

public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Proof.X448.AArch64.Setup
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.X448.AArch64.Mul

/-! ### `Ed448.AArch64.VerifyChunks`, which only this module used -/

section

/-!
# Ed448 verification's equation on AArch64: seven-byte chunks

`bytes7 rp o`: the seven bytes at `rp + o` as one 56-bit number (`chunk7`),
from the highest (X448's `suffix`). `carryK rp o K`: the carry out of the 56
bytes at `rp + o` plus `K`, chunk by chunk (`carryK_ok`): 0 exactly when
their sum is below `2^448`.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Keeps read1_eq)
open VG.Proof.X25519 (leNum leNum_append leNum_lt)

/-- The seven bytes at `q`, little-endian. -/
abbrev chunk7 (m : Mem) (q : Addr) : Nat := leNum (Spec.X448.bytesAt m q 7)

theorem chunk7_lt (m : Mem) (q : Addr) : chunk7 m q < 2 ^ 56 := by
  have h := leNum_lt (Spec.X448.bytesAt m q 7)
  rw [VG.Proof.X448.length_bytesAt] at h
  exact Nat.lt_of_lt_of_le h (by decide)

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
theorem byte7_ok {s : State} {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (h4 : rp ≠ .x4) {o j : Nat}
    (ho : o + 7 ≤ 4096) (hj : j < 7) (hb : (s.gpr .x4).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (o + (6 - j))) 1) :
    WP isa (.block ([.lsl .x .x4 .x4 8, .ldrb .x7 rp (o + (6 - j)), .add .x .x4 .x4 .x7] : List Instr)) s
      fun t => (t.gpr .x4).toNat = 256 * (s.gpr .x4).toNat + (s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).toNat ∧
        t.mem = s.mem ∧ Keeps [.x4, .x7] s t := by
  have byteb := (s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).isLt
  have mulb : (s.gpr .x4).toNat * 256 < 2 ^ 64 := by omega
  have enc : (o + (6 - j)) % 1 = 0 ∧ o + (6 - j) < 4096 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, h4, hp,
    State.load, hr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    change (((s.gpr .x4).toNat * 256) % 2 ^ 64 +
      ((s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).toNat % 2 ^ 32) % 2 ^ 64) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt mulb, Nat.mod_eq_of_lt (by omega : (s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).toNat < 2 ^ 64)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem zero4_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t => (t.gpr .x4).toNat = 0 ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- `bytes7 rp o`: `x4` is the chunk at `rp + o`. -/
theorem bytes7_ok {s : State} {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (h4 : rp ≠ .x4) (h7 : rp ≠ .x7)
    {o : Nat} (ho : o + 7 ≤ 4096) (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (o + j)) 1) :
    WP isa (.block (bytes7 rp o)) s fun t =>
      (t.gpr .x4).toNat = chunk7 s.mem (p + BitVec.ofNat 64 o) ∧ t.mem = s.mem ∧ Keeps [.x4, .x7] s t := by
  rw [bytes7, WP.block_append_iff]
  refine WP.mono (zero4_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x4).toNat = VG.Proof.X448.suffix s.mem (p + BitVec.ofNat 64 o) 0 n ∧ u.mem = s.mem ∧
      Keeps [.x4, .x7] t u
  have step : ∀ n u, n < 7 → inv n u →
      WP isa (.block ([.lsl .x .x4 .x4 8, .ldrb .x7 rp (o + (6 - n)), .add .x .x4 .x4 .x7] : List Instr)) u
        (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr rp = p := by
      rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩),
        tk.1 _ (by simp only [List.mem_singleton]; exact h4)]
      exact hp
    have ub : (u.gpr .x4).toNat < 2 ^ 48 := by
      rw [uv]
      have h := VG.Proof.X448.suffix_bound s.mem (p + BitVec.ofNat 64 o) 0 n
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega_using [hn])
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 (o + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega_using [])
    refine WP.mono (byte7_ok up h4 ho hn ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [vv, uv, um, VG.Proof.X448.suffix_succ _ _ _ hn, Offset.add_add]
    simp only [Nat.mul_zero, Nat.zero_add]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) t
    ⟨by rw [tz]; rfl, tm, VG.Proof.X448.AArch64.Keeps.refl _ _⟩) fun u ⟨uv, um, uk⟩ => ⟨?_, um, ?_⟩
  · rw [uv]; simp only [VG.Proof.X448.suffix, Nat.mul_zero, Nat.zero_add, Nat.sub_self, BitVec.add_zero]
  · refine (tk.mono ?_).trans uk
    intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

/-- `x4 += x6 + x5`, and the carry out of 56 bits into `x5`. -/
theorem carryStep_ok {s : State} {a k c : Nat} (ha : (s.gpr .x4).toNat = a) (hk : (s.gpr .x6).toNat = k)
    (hc : (s.gpr .x5).toNat = c) (ha' : a < 2 ^ 56) (hk' : k < 2 ^ 56) (hc' : c < 2 ^ 56) :
    WP isa (.block ([.add .x .x4 .x4 .x6, .add .x .x4 .x4 .x5, .lsr .x .x5 .x4 56] : List Instr)) s fun t =>
      (t.gpr .x5).toNat = (a + k + c) / 2 ^ 56 ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceLT,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write, ite_true,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, ha, hk, hc, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega_using [ha', hk'] : a + k < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [ha', hk', hc'] : a + k + c < 2 ^ 64)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem carry_div (A a k n : Nat) :
    (A + 2 ^ (56 * n) * (a + k)) / 2 ^ (56 * (n + 1)) = (a + k + A / 2 ^ (56 * n)) / 2 ^ 56 := by
  rw [show 56 * (n + 1) = 56 * n + 56 by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (A / _)]

theorem pow256 (n : Nat) : (256 : Nat) ^ (7 * n) = 2 ^ (56 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (7 * n) = 56 * n by omega_using []]

/-- The carry after one more chunk. -/
theorem carry_next (A B a k n : Nat) :
    (a + k + (A + B) / 2 ^ (56 * n)) / 2 ^ 56 =
      ((A + 2 ^ (56 * n) * a) + (B + 2 ^ (56 * n) * k)) / 2 ^ (56 * (n + 1)) := by
  rw [Nat.add_add_add_comm, ← Nat.mul_add, carry_div]

theorem mod_succ56 (K n : Nat) :
    K % 2 ^ (56 * (n + 1)) = K % 2 ^ (56 * n) + 2 ^ (56 * n) * ((K >>> (56 * n)) % 2 ^ 56) := by
  rw [show 56 * (n + 1) = 56 * n + 56 by omega_using [], Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow]

theorem leNum_chunks (m : Mem) (q : Addr) (n : Nat) :
    leNum (Spec.X448.bytesAt m q (7 * (n + 1))) =
      leNum (Spec.X448.bytesAt m q (7 * n)) + 2 ^ (56 * n) * chunk7 m (q + BitVec.ofNat 64 (7 * n)) := by
  rw [show 7 * (n + 1) = 7 * n + 7 by omega_using [], VG.Proof.X448.bytesAt_add, leNum_append,
    VG.Proof.X448.length_bytesAt, pow256]

/-- `carryK rp o K`: `x5` is the carry out of the 56 bytes at `rp + o` plus `K`. -/
theorem carryK_ok {s : State} {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (hrp : rp ≠ .x4 ∧ rp ≠ .x5 ∧ rp ≠ .x6 ∧ rp ≠ .x7) {o K : Nat} (ho : o + 56 ≤ 4096)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (o + j)) 1) :
    WP isa (.block (carryK rp o K)) s fun t =>
      (t.gpr .x5).toNat = (leNum (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 o) 56) + K % 2 ^ 448) / 2 ^ 448 ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7] s t := by
  obtain ⟨h4, h5, h6, h7⟩ := hrp
  let q := p + BitVec.ofNat 64 o
  rw [carryK, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .x .x5 0 0]) s fun t =>
      (t.gpr .x5).toNat = 0 ∧ t.mem = s.mem ∧ Keeps [.x5] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x5).toNat = (leNum (Spec.X448.bytesAt s.mem q (7 * n)) + K % 2 ^ (56 * n)) / 2 ^ (56 * n) ∧
      u.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7] t u
  have step : ∀ n u, n < 8 → inv n u →
      WP isa (.block (bytes7 rp (o + 7 * n) ++
        Impl.X448.AArch64.Base.const64 .x6 (BitVec.ofNat 64 ((K >>> (56 * n)) % 2 ^ 56)) ++
        ([.add .x .x4 .x4 .x6, .add .x .x4 .x4 .x5, .lsr .x .x5 .x4 56] : List Instr))) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr rp = p := by
      rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h5, h6, h7⟩),
        tk.1 _ (by simp only [List.mem_singleton]; exact h5)]
      exact hp
    have cb : (u.gpr .x5).toNat ≤ 1 := by
      rw [uv]
      have h1 := leNum_lt (Spec.X448.bytesAt s.mem q (7 * n))
      rw [VG.Proof.X448.length_bytesAt, pow256] at h1
      have h2 := Nat.mod_lt K (Nat.two_pow_pos (56 * n))
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega_using [h1]))
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (bytes7_ok up h4 h7 (o := o + 7 * n) (by omega_using [ho, hn]) (fun j hj => by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2, Nat.add_assoc]; exact hr (7 * n + j) (by omega_using [hn, hj])))
      fun v ⟨v4, vm, vk⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.AArch64.Tbl.const64_ok v .x6 (BitVec.ofNat 64 ((K >>> (56 * n)) % 2 ^ 56)))
      fun w ⟨w6, wg, we⟩ => ?_
    have w4 : (w.gpr .x4).toNat = chunk7 s.mem (q + BitVec.ofNat 64 (7 * n)) := by
      rw [wg _ (by decide), v4, um, Offset.add_add]
    have w5 : (w.gpr .x5).toNat = (u.gpr .x5).toNat := by
      rw [wg _ (by decide), vk.1 _ (by decide)]
    have kl : (K >>> (56 * n)) % 2 ^ 56 < 2 ^ 56 := Nat.mod_lt _ (by decide)
    have w6' : (w.gpr .x6).toNat = (K >>> (56 * n)) % 2 ^ 56 := by
      rw [w6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
    refine WP.mono (carryStep_ok w4 w6' w5 (chunk7_lt _ _) kl (by omega_using [cb])) fun x ⟨x5, xm, xk⟩ => ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [x5, uv, leNum_chunks, mod_succ56]
      exact carry_next _ _ _ _ _
    · rw [xm, show w.mem = v.mem by rw [we], vm, um]
    · refine uk.trans ((vk.mono ?_).trans (?_ : Keeps [.x4, .x5, .x6, .x7] v w) |>.trans (xk.mono ?_))
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp
      · exact ⟨fun r hr => wg r (by rintro rfl; exact hr (by simp)), by rw [we], by rw [we]⟩
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) t
    ⟨by rw [tz]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.add_zero]; rfl, tm, VG.Proof.X448.AArch64.Keeps.refl _ _⟩)
    fun u ⟨uv, um, uk⟩ => ⟨by simp only [Nat.reduceMul] at uv; exact uv, um, ?_⟩
  exact (tk.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)).trans uk

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 verification's equation on AArch64: checks of the encodings' bytes

`sCheck`: `S < L` for the 57 bytes at `x1 + 57` (`carryK` of `2^448 - L`, and
byte 56). `decodeY`: the 56 bytes of `y` as eight seven-byte chunks in a
slot, `y < p` (`carryK` of `2^224 + 1`), bits 448–454 zero, and the sign bit
in `x17`.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X25519 (leNum)
open VG.Impl.X448.AArch64 (ld st slot)

theorem ldrb5_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p) {o : Nat} (ho : o < 4096)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 o) 1) :
    WP isa (.block [.ldrb .x5 rp o]) s fun t =>
      t.gpr .x5 = (s.mem (p + BitVec.ofNat 64 o)).setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x5] s t := by
  have enc : o % 1 = 0 ∧ o < 4096 := ⟨Nat.mod_one _, ho⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self, hp, State.load, hr,
    VG.Proof.X448.AArch64.read1_eq, RegUpd.gpr_write, RegUpd.mem_write,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, Size.bits]
    have := (s.mem (p + BitVec.ofNat 64 o)).isLt
    omega_arith
  · simp only [List.mem_singleton] at hr
    simp only [State.write, hr, ite_false]

theorem setWidth8_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b.toNat = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)), h]; rfl

theorem bytesAt_succ57 (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [Spec.Ed448.bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- `sCheck`: `x20 |= c`, with `c = 0` exactly when the 57 bytes at `x1 + 57` are below `L`. -/
theorem sCheck_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (57 + j)) 1) :
    WP isa (.block sCheck) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (p + BitVec.ofNat 64 57) 57) <
        Spec.Ed448.L) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x20] s t := by
  rw [sCheck]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryK_ok (rp := .x1) (o := 57) hp (by decide) (by decide)
    (fun j hj => hr j (by omega_arith))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  rw [WP.block_append_iff]
  have pv : v.gpr .x1 = p := by rw [vk.1 _ (by decide), uk.1 _ (by decide)]; exact hp
  refine WP.mono (ldrb5_ok v pv (o := 113) (by decide) (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2]; exact hr 56 (by decide))) fun w ⟨w5, wm, wk⟩ => ?_
  refine WP.mono (orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  generalize hy : leNum (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y at u5
  have hyl : y < 2 ^ 448 := by
    rw [← hy]
    have := VG.Proof.X25519.leNum_lt (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56)
    rw [VG.Proof.X448.length_bytesAt] at this
    exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
  have hK : (2 ^ 448 - Spec.Ed448.L) % 2 ^ 448 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel
  rw [hK] at u5
  have hb : v.mem (p + BitVec.ofNat 64 113) = s.mem (p + BitVec.ofNat 64 113) := by rw [vm, um]
  refine ⟨⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, ?_, ?_⟩
  · rw [VG.Proof.Ed448.AArch64.or_eq_zero64, w5, hb, setWidth8_eq_zero, bytesAt_succ57, decodeLE_append,
      Offset.add_add, VG.Proof.X448.length_bytesAt]
    rw [show Spec.Ed448.decodeLE [s.mem (p + BitVec.ofNat 64 (57 + 56))] = (s.mem (p + BitVec.ofNat 64 113)).toNat by
      simp [Spec.Ed448.decodeLE]]
    rw [show Spec.Ed448.decodeLE (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y by
      rw [← hy, decodeLE_eq]]
    have h1 := Nat.mod_add_div (y + (2 ^ 448 - Spec.Ed448.L)) (2 ^ 448)
    have h2 := Nat.mod_lt (y + (2 ^ 448 - Spec.Ed448.L)) (Nat.two_pow_pos 448)
    have h3 : (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 448)]
      have := Nat.sub_le (2 ^ 448) Spec.Ed448.L
      omega_arith
    have key := sCheck_nat (b := (s.mem (p + BitVec.ofNat 64 113)).toNat) hyl h2 h3 h1
    rw [← key]
    have hu : u.gpr .x5 = 0 ↔ (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 = 0 := by
      rw [← u5]
      exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hu]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), BitVec.or_assoc]
  · rw [tm, wm, vm, um]
  · exact (((uk.mono (by decide)).trans (vk.mono (by decide))).trans (wk.mono (by decide))).trans (tk.mono (by decide))

/-! ## `y` -/

theorem wide_chunks (m : Mem) (q : Addr) :
    ∀ n, VG.Proof.X448.Wide.valN (fun i => chunk7 m (q + BitVec.ofNat 64 (7 * i))) n =
      leNum (Spec.X448.bytesAt m q (7 * n))
  | 0 => rfl
  | n + 1 => by
    rw [VG.Proof.X448.Wide.valN_succ, wide_chunks m q n, leNum_chunks]
    congr 2
    rw [VG.Proof.X448.Wide.radix, ← Nat.pow_mul]

theorem byte56_val (b : Byte) :
    (b.setWidth 64 >>> 7) = BitVec.ofNat 64 (b.toNat / 128) ∧
      (b.setWidth 64 &&& BitVec.setWidth 64 (0x7f : BitVec 16)) = BitVec.ofNat 64 (b.toNat % 128) := by
  have hb := b.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (BitVec.toNat (127 : BitVec 16)) % 2 ^ 64 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega_arith : b.toNat % 2 ^ 7 < 2 ^ 64)]
    omega_arith

/-- Byte 56: the sign bit into `x17`, and bits 448–454 into `x5`. -/
theorem byte56_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0,
        .logic .and .x .x5 .x5 .x6] : List Instr)) s fun t =>
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      t.gpr .x5 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ∧
      t.mem = s.mem ∧ Keeps [.x5, .x6, .x17] s t := by
  rw [show ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] : List Instr) =
    [.ldrb .x5 rp 56] ++ [.lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldrb5_ok s hp (o := 56) (by decide) hr) fun u ⟨u5, um, uk⟩ => ?_
  have bv := byte56_val (s.mem (p + BitVec.ofNat 64 56))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceMul,
    Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq, RegUpd.gpr_write, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left', u5]
  refine ⟨bv.1, bv.2, um, (fun r hr => ?_), uk.2.1, uk.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.1, hr.2.1, hr.2.2, ite_false]
  exact uk.1 r (by simp only [List.mem_singleton]; exact hr.1)

/-- The chunks of `y` into slot `yo`. -/
theorem yStores_ok {s : State} {base : Addr} (hs : Scr s base) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (h4 : rp ≠ .x4) (h7 : rp ≠ .x7) (yo : Fin 22)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 8).flatMap (fun i => bytes7 rp (7 * i) ++ [st .x4 (slot yo.val + 8 * i)]))) s
      fun t => (∀ i < 8, (word t.mem base (slot yo.val + 8 * i)).toNat = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
        Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t := by
  have hy := yo.isLt
  let inv := fun n (t : State) =>
    (∀ i < n, (word t.mem base (slot yo.val + 8 * i)).toNat = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
      Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (bytes7 rp (7 * n) ++ [st .x4 (slot yo.val + 8 * n)])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    have tp : t.gpr rp = p := by
      rw [tk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
    have hst : Scr t base := hs.of_keeps tk (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (bytes7_ok tp h4 h7 (o := 7 * n) (by omega_arith) (fun j hj => by
      rw [tk.2.1, tk.2.2]; exact hr _ (by omega_arith))) fun u ⟨u4, um, uk⟩ => ?_
    have hsu : Scr u base := hst.of_keeps uk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.store_ok hsu (d := slot yo.val + 8 * n) (by simp only [slot]; omega_arith)
      (by simp only [slot]; omega_arith) .x4) fun v ⟨vm, vk⟩ => ⟨fun i hi => ?_, ?_, (tk.trans uk).trans (vk.mono (by simp))⟩
    · rw [vm, VG.Proof.X448.AArch64.word_write_aligned _ _ (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
        (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)]
      by_cases h : i = n
      · subst h
        rw [ite_eq_left rfl, u4]
        have hc : chunk7 t.mem (p + BitVec.ofNat 64 (7 * i)) = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i)) := by
          apply congrArg leNum
          simp only [Spec.X448.bytesAt]
          refine List.map_congr_left fun j hj => ?_
          have hj := List.mem_range.mp hj
          rw [Offset.add_add]
          exact tm _ (Or.inr (by have := hfar (7 * i + j) (by omega_arith); simp only [slot] at *; omega_arith))
        exact hc
      · rw [ite_eq_right (by omega_arith), um]; exact tv i (by omega_arith)
    · intro x hx
      rw [vm, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [slot]; omega_arith) x (by omega_arith), um]
      exact tm x hx
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), VG.Proof.X448.AArch64.Outside.refl _ _ _ _,
      VG.Proof.X448.AArch64.Keeps.refl _ _⟩

theorem P_add : Spec.X448.P + (2 ^ 224 + 1) = 2 ^ 448 := by decide +kernel

/-- `decodeY rp yo`: `y` (the first 56 bytes at `rp`) in slot `yo`, the sign bit in `x17`, and
`x20 |= c`, `c = 0` exactly when bits 448–454 are 0 and `y < p`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base) {rp : Reg}
    {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (yo : Fin 22)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block (decodeY rp yo.val)) s fun t =>
      E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ i : Fin 22, i ≠ yo → E t.mem base i = E s.mem base i) ∧
      (∀ j < 8, VG.Proof.X448.AArch64.limbs t.mem base (slot yo.val) j < 2 ^ 56) ∧
      Keeps [.x4, .x5, .x6, .x7, .x17, .x20] s t ∧ Outside base (slot yo.val) 64 s.mem t.mem := by
  have hy := yo.isLt
  have h4 : rp ≠ .x4 := by rcases hrp with rfl | rfl <;> decide
  have h5 : rp ≠ .x5 := by rcases hrp with rfl | rfl <;> decide
  have h6 : rp ≠ .x6 := by rcases hrp with rfl | rfl <;> decide
  have h7 : rp ≠ .x7 := by rcases hrp with rfl | rfl <;> decide
  rw [decodeY]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yStores_ok hs hp h4 h7 yo (fun j hj => hr j (by omega_arith)) (fun j hj => hfar j (by omega_arith)))
    fun a ⟨av, am, ak⟩ => ?_
  have hin : ∀ j < 57, a.mem (p + BitVec.ofNat 64 j) = s.mem (p + BitVec.ofNat 64 j) := fun j hj =>
    am _ (Or.inr (by have := hfar j hj; simp only [slot] at *; omega_arith))
  have ap : a.gpr rp = p := by
    rw [ak.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (carryK_ok (o := 0) ap ⟨h4, h5, h6, h7⟩ (by decide) (fun j hj => by
    rw [ak.2.1, ak.2.2, Nat.zero_add]; exact hr j (by omega_arith))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  have vp : v.gpr rp = p := by
    rw [vk.1 _ (by simp only [List.mem_singleton]; rcases hrp with rfl | rfl <;> decide),
      uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h5, h6, h7⟩)]
    exact ap
  rw [WP.block_append_iff]
  refine WP.mono (byte56_ok v vp (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2, ak.2.1, ak.2.2]; exact hr 56 (by decide))) fun w ⟨w17, w5, wm, wk⟩ => ?_
  refine WP.mono (orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  have hb56 : v.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [vm, um]; exact hin 56 (by decide)
  have hy56 : leNum (Spec.X448.bytesAt a.mem (p + BitVec.ofNat 64 0) 56) =
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [BitVec.add_zero, decodeLE_eq]
    apply congrArg leNum
    simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt]
    exact List.map_congr_left fun j hj => hin j (by have := List.mem_range.mp hj; omega_arith)
  have tmem : t.mem = a.mem := by rw [tm, wm, vm, um]
  -- The value of slot `yo`.
  have ey : E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) := by
    have w8 := wide_chunks s.mem p 8
    rw [show 7 * 8 = 56 from rfl] at w8
    rw [decodeLE_eq, show Spec.Ed448.bytesAt s.mem p 56 = Spec.X448.bytesAt s.mem p 56 from rfl, ← w8, tmem]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun i hi => av i hi)
  refine ⟨ey, ?_, ⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, fun i hi => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [tk.1 _ (by decide), w17, hb56]
  · rw [or_eq_zero64, w5, hb56]
    have hc : (u.gpr .x5).toNat = (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) + (2 ^ 224 + 1)) / 2 ^ 448 := by
      rw [u5, hy56, show ((2 : Nat) ^ 224 + 1) % 2 ^ 448 = 2 ^ 224 + 1 by decide +kernel]
    have hylt : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < 2 ^ 448 := by
      have := decodeLE_lt' (Spec.Ed448.bytesAt s.mem p 56)
      rw [show (Spec.Ed448.bytesAt s.mem p 56).length = 56 by simp [Spec.Ed448.bytesAt]] at this
      exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
    have hP := P_add
    generalize Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) = y at hc hylt ⊢
    generalize (2 : Nat) ^ 448 = M at hc hylt hP
    have e1 : u.gpr .x5 = 0 ↔ y < Spec.X448.P := by
      constructor
      · intro h
        rw [h] at hc
        have : (y + (2 ^ 224 + 1)) / M = 0 := hc.symm
        rw [Nat.div_eq_zero_iff_lt (by omega_arith)] at this
        omega_arith
      · intro h
        apply BitVec.eq_of_toNat_eq
        rw [hc, Nat.div_eq_of_lt (by omega_arith)]; rfl
    have e2 : BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) = 0 ↔
        (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      · intro h; rw [h]; rfl
    rw [e1, e2, and_comm]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), ak.1 _ (by decide), BitVec.or_assoc]
  · rw [tmem]
    exact VG.Proof.X448.AArch64.Weak.E_outside am i
      (by have := VG.Proof.X448.AArch64.Weak.slot_sep hi; omega_arith)
  · rw [tmem]
    change (word a.mem base (slot yo.val + 8 * j)).toNat < _
    rw [av j hj]
    exact chunk7_lt _ _
  · exact ((((ak.mono (by decide)).trans (uk.mono (by decide))).trans (vk.mono (by decide))).trans
      (wk.mono (by decide))).trans (tk.mono (by decide))
  · rw [tmem]; exact am

end VG.Proof.Ed448.AArch64
