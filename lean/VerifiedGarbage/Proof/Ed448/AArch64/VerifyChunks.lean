import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.Pairs
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-!
# Ed448 verification's equation on AArch64: seven-byte chunks

`bytes7 rp o`: the seven bytes at `rp + o` as one 56-bit number (`chunk7`),
from the highest (X448's `suffix`). `carryK rp o K`: the carry out of the 56
bytes at `rp + o` plus `K`, chunk by chunk (`carryK_ok`): 0 exactly when
their sum is below `2^448`.
-/

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
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 (o + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega)
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
    rw [Nat.mod_eq_of_lt (by omega : a + k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a + k + c < 2 ^ 64)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem carry_div (A a k n : Nat) :
    (A + 2 ^ (56 * n) * (a + k)) / 2 ^ (56 * (n + 1)) = (a + k + A / 2 ^ (56 * n)) / 2 ^ 56 := by
  rw [show 56 * (n + 1) = 56 * n + 56 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (A / _)]

theorem pow256 (n : Nat) : (256 : Nat) ^ (7 * n) = 2 ^ (56 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (7 * n) = 56 * n by omega]

/-- The carry after one more chunk. -/
theorem carry_next (A B a k n : Nat) :
    (a + k + (A + B) / 2 ^ (56 * n)) / 2 ^ 56 =
      ((A + 2 ^ (56 * n) * a) + (B + 2 ^ (56 * n) * k)) / 2 ^ (56 * (n + 1)) := by
  rw [Nat.add_add_add_comm, ← Nat.mul_add, carry_div]

theorem mod_succ56 (K n : Nat) :
    K % 2 ^ (56 * (n + 1)) = K % 2 ^ (56 * n) + 2 ^ (56 * n) * ((K >>> (56 * n)) % 2 ^ 56) := by
  rw [show 56 * (n + 1) = 56 * n + 56 by omega, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow]

theorem leNum_chunks (m : Mem) (q : Addr) (n : Nat) :
    leNum (Spec.X448.bytesAt m q (7 * (n + 1))) =
      leNum (Spec.X448.bytesAt m q (7 * n)) + 2 ^ (56 * n) * chunk7 m (q + BitVec.ofNat 64 (7 * n)) := by
  rw [show 7 * (n + 1) = 7 * n + 7 by omega, VG.Proof.X448.bytesAt_add, leNum_append,
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
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega))
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (bytes7_ok up h4 h7 (o := o + 7 * n) (by omega) (fun j hj => by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2, Nat.add_assoc]; exact hr (7 * n + j) (by omega)))
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
      rw [w6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine WP.mono (carryStep_ok w4 w6' w5 (chunk7_lt _ _) kl (by omega)) fun x ⟨x5, xm, xk⟩ => ?_
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
