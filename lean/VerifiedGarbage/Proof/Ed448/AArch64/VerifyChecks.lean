import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.BaseField`. -/
section

/-!
# Ed448 base-point multiplication on AArch64: field programs

A list of field operations on the slots (`FOp`) runs as X448's field
arithmetic on AArch64 (`mulE`, `addE`, `subE`): the slots become the
operations' evaluation (`evalOps`, `Proof/Ed448/Formulas.lean`), their limbs
stay below `2^56 + 32` (`BoundedEnv`), and nothing else changes but the
registers `workRegs` and the memory of the slots and of the products'
coefficients (`Keep`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv mulE addE subE)

theorem slot_idx {n : Nat} (h : n < 22) :
    Impl.X448.AArch64.slot n = Impl.X448.AArch64.slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (op : FOp)
    (hv : fopValid op) :
    WP isa (Impl.X448.AArch64.Weak.code (toOp op)) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = VG.Proof.Ed448.evalOp op (E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, VG.Proof.Ed448.AArch64.slot_idx h1, VG.Proof.Ed448.AArch64.slot_idx h2, VG.Proof.Ed448.AArch64.slot_idx h3]
    exact mulE hs hb _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, VG.Proof.Ed448.AArch64.slot_idx h1, VG.Proof.Ed448.AArch64.slot_idx h2]
    exact mulE hs hb _ _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, VG.Proof.Ed448.AArch64.slot_idx h1, VG.Proof.Ed448.AArch64.slot_idx h2, VG.Proof.Ed448.AArch64.slot_idx h3]
    exact addE hs hb _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.AArch64.Weak.code, VG.Proof.Ed448.AArch64.slot_idx h1, VG.Proof.Ed448.AArch64.slot_idx h2, VG.Proof.Ed448.AArch64.slot_idx h3]
    exact subE hs hb _ _ _

theorem field_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa (VG.Impl.Ed448.AArch64.field ops) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = VG.Proof.Ed448.evalOps ops (E s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨VG.Proof.X448.AArch64.Keep.refl _ _, hb, rfl⟩
  | cons op ops ih =>
    change WP isa (.seq (Impl.X448.AArch64.Weak.code (toOp op)) (VG.Impl.Ed448.AArch64.field ops)) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.fop_ok hs hb op (hv op List.mem_cons_self)) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (tk.scr hs) tb)
      fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]; rfl⟩

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.BaseEncode`. -/
section

/-!
# Ed448 on AArch64: the encoding's sign byte

The sign of `x` as the top bit of an encoding's byte 56 (`signByte_ok`), from
the low bit of a fully reduced element (`valN_mod_two`), and an encoding's 57
bytes as its first 56 and byte 56 (`bytesAt_57`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 Saved ofs workRegs
  write1_eq writeW8_apply)
open VG.Proof.X448.AArch64.Weak (E F BoundedEnv FieldOp applyOps opMul opCopy invEnv invEnv_eval
  invEnv_x2 invert_ok ops_ok IKeep)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC TMP)

theorem signByte_val (w : BitVec 64) :
    (((w <<< 63) >>> 56).setWidth 32).setWidth 8 = BitVec.ofNat 8 (128 * (w.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := w.isLt
  omega

/-- The top bit of byte 56 of the output: the low bit of `X2`'s first word. -/
theorem signByte_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x1 = p)
    (hw : InRegions s.wr (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([ld .x4 X2, .lsl .x .x4 .x4 63, .lsr .x .x4 .x4 56, .strb .x4 .x1 56] : List Instr)) s
      fun t => t.mem = s.mem.writeW (p + BitVec.ofNat 64 56)
          (BitVec.ofNat 8 (128 * ((word s.mem base X2).toNat % 2))) ∧ Keeps [.x4] s t := by
  have hr := hs.read (d := X2) (n := 8) (by decide)
  have enc : X2 % 8 = 0 ∧ X2 < 4096 * 8 := by decide
  have enc1 : (56 : Nat) % 1 = 0 ∧ (56 : Nat) < 4096 * 1 := by decide
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.store, State.read, enc, enc1, and_self, BitVec.setWidth_eq, hs.x3, hp, hr, hw,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.reduceLT, Nat.reduceMul,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, write1_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [VG.Proof.Ed448.AArch64.signByte_val]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- A legacy slot (sixteen limbs below `2^28`) is a weak one. -/
theorem bounded_of_legacy {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.X448.AArch64.Bounded m base o) :
    VG.Proof.Curve448.AArch64.Bounded m base o := fun i hi =>
  Nat.lt_trans (h i (by omega)) (by decide)

/-- The low bit of sixteen 28-bit limbs is that of the first. -/
theorem valN_mod_two (f : Nat → Nat) : VG.Proof.X448.valN f 16 % 2 = f 0 % 2 := by
  rw [show (16 : Nat) = 1 + 15 from rfl, VG.Proof.X448.valN_split]
  simp only [VG.Proof.X448.valN, VG.Proof.X448.radix, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]
  omega

theorem bytesAt_57 (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 57 = Spec.X448.bytesAt m p 56 ++ [m (p + BitVec.ofNat 64 56)] := by
  rw [VG.Proof.Ed448.bytesAt_eq]
  simp only [Spec.X25519.bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyChunks`. -/
section

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

theorem chunk7_lt (m : Mem) (q : Addr) : VG.Proof.Ed448.AArch64.chunk7 m q < 2 ^ 56 := by
  have h := leNum_lt (Spec.X448.bytesAt m q 7)
  rw [VG.Proof.X448.length_bytesAt] at h
  exact Nat.lt_of_lt_of_le h (by decide)

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
theorem byte7_ok {s : State} {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (h4 : rp ≠ .x4) {o j : Nat}
    (ho : o + 7 ≤ 4096) (hj : j < 7) (hb : (s.gpr .x4).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (o + (6 - j))) 1) :
    WP isa (.block ([.lsl .x .x4 .x4 8, .ldrb .x7 rp (o + (6 - j)), .add .x .x4 .x4 .x7] : List Instr)) s
      fun t => (t.gpr .x4).toNat = 256 * (s.gpr .x4).toNat + (s.mem (p + BitVec.ofNat 64 (o + (6 - j)))).toNat ∧
        t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x7] s t := by
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
    WP isa (.block [.movz .x .x4 0 0]) s fun t => (t.gpr .x4).toNat = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4] s t := by
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
      (t.gpr .x4).toNat = VG.Proof.Ed448.AArch64.chunk7 s.mem (p + BitVec.ofNat 64 o) ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x7] s t := by
  rw [bytes7, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.zero4_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x4).toNat = VG.Proof.X448.suffix s.mem (p + BitVec.ofNat 64 o) 0 n ∧ u.mem = s.mem ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x7] t u
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
    refine WP.mono (VG.Proof.Ed448.AArch64.byte7_ok up h4 ho hn ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
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
      (t.gpr .x5).toNat = (a + k + c) / 2 ^ 56 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
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
  rw [Nat.add_add_add_comm, ← Nat.mul_add, VG.Proof.Ed448.AArch64.carry_div]

theorem mod_succ56 (K n : Nat) :
    K % 2 ^ (56 * (n + 1)) = K % 2 ^ (56 * n) + 2 ^ (56 * n) * ((K >>> (56 * n)) % 2 ^ 56) := by
  rw [show 56 * (n + 1) = 56 * n + 56 by omega, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow]

theorem leNum_chunks (m : Mem) (q : Addr) (n : Nat) :
    leNum (Spec.X448.bytesAt m q (7 * (n + 1))) =
      leNum (Spec.X448.bytesAt m q (7 * n)) + 2 ^ (56 * n) * VG.Proof.Ed448.AArch64.chunk7 m (q + BitVec.ofNat 64 (7 * n)) := by
  rw [show 7 * (n + 1) = 7 * n + 7 by omega, VG.Proof.X448.bytesAt_add, leNum_append,
    VG.Proof.X448.length_bytesAt, VG.Proof.Ed448.AArch64.pow256]

/-- `carryK rp o K`: `x5` is the carry out of the 56 bytes at `rp + o` plus `K`. -/
theorem carryK_ok {s : State} {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (hrp : rp ≠ .x4 ∧ rp ≠ .x5 ∧ rp ≠ .x6 ∧ rp ≠ .x7) {o K : Nat} (ho : o + 56 ≤ 4096)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (o + j)) 1) :
    WP isa (.block (carryK rp o K)) s fun t =>
      (t.gpr .x5).toNat = (leNum (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 o) 56) + K % 2 ^ 448) / 2 ^ 448 ∧
      t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x6, .x7] s t := by
  obtain ⟨h4, h5, h6, h7⟩ := hrp
  let q := p + BitVec.ofNat 64 o
  rw [carryK, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .x .x5 0 0]) s fun t =>
      (t.gpr .x5).toNat = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x5] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x5).toNat = (leNum (Spec.X448.bytesAt s.mem q (7 * n)) + K % 2 ^ (56 * n)) / 2 ^ (56 * n) ∧
      u.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x6, .x7] t u
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
      rw [VG.Proof.X448.length_bytesAt, VG.Proof.Ed448.AArch64.pow256] at h1
      have h2 := Nat.mod_lt K (Nat.two_pow_pos (56 * n))
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega))
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.bytes7_ok up h4 h7 (o := o + 7 * n) (by omega) (fun j hj => by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2, Nat.add_assoc]; exact hr (7 * n + j) (by omega)))
      fun v ⟨v4, vm, vk⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.AArch64.Tbl.const64_ok v .x6 (BitVec.ofNat 64 ((K >>> (56 * n)) % 2 ^ 56)))
      fun w ⟨w6, wg, we⟩ => ?_
    have w4 : (w.gpr .x4).toNat = VG.Proof.Ed448.AArch64.chunk7 s.mem (q + BitVec.ofNat 64 (7 * n)) := by
      rw [wg _ (by decide), v4, um, Offset.add_add]
    have w5 : (w.gpr .x5).toNat = (u.gpr .x5).toNat := by
      rw [wg _ (by decide), vk.1 _ (by decide)]
    have kl : (K >>> (56 * n)) % 2 ^ 56 < 2 ^ 56 := Nat.mod_lt _ (by decide)
    have w6' : (w.gpr .x6).toNat = (K >>> (56 * n)) % 2 ^ 56 := by
      rw [w6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine WP.mono (VG.Proof.Ed448.AArch64.carryStep_ok w4 w6' w5 (VG.Proof.Ed448.AArch64.chunk7_lt _ _) kl (by omega)) fun x ⟨x5, xm, xk⟩ => ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [x5, uv, VG.Proof.Ed448.AArch64.leNum_chunks, VG.Proof.Ed448.AArch64.mod_succ56]
      exact VG.Proof.Ed448.AArch64.carry_next _ _ _ _ _
    · rw [xm, show w.mem = v.mem by rw [we], vm, um]
    · refine uk.trans ((vk.mono ?_).trans (?_ : VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x6, .x7] v w) |>.trans (xk.mono ?_))
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

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks`. -/
section

/-!
# Ed448 verification's equation on AArch64: the checks

Each check ORs into `x20` a word that is 0 exactly when it passes
(`orBad`). A comparison of two slots (`eqSlots`) reduces each fully into `X2`
(`canon`: X448's `toLegacy` and `freeze`, sixteen 28-bit limbs), keeping the
first in `CAN`, and ORs the XORs of the limbs (`diffCan`): fully reduced
elements are equal exactly when their limbs are. Checks write only `X2`,
`CAN` and the products' coefficients (`CFrame`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-! ## What checks write -/

/-- Memory beyond `X2`, `CAN` and the coefficients is unchanged. -/
def CFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < X2 ∨ X2 + 128 ≤ ofs base x) → (ofs base x < CAN ∨ CAN + 128 ≤ ofs base x) →
    (ofs base x < ACC ∨ ACC + 512 ≤ ofs base x) → m' x = m x

theorem CFrame.refl (base : Addr) (m : Mem) : CFrame base m m := fun _ _ _ _ => rfl

theorem CFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : CFrame base m₁ m₂) (h₂ : CFrame base m₂ m₃) :
    CFrame base m₁ m₃ := fun x a b c => (h₂ x a b c).trans (h₁ x a b c)

theorem CFrame.of_field {base : Addr} {m m' : Mem} (h : FieldMem base X2 m m') : CFrame base m m' :=
  fun x a _ c => h x a c

theorem CFrame.of_can {base : Addr} {m m' : Mem} (h : Outside base CAN 128 m m') : CFrame base m m' :=
  fun x _ b _ => h x b

theorem CFrame.word {base : Addr} {m m' : Mem} (h : CFrame base m m') {d : Nat}
    (h1 : d + 8 ≤ X2 ∨ X2 + 128 ≤ d) (h2 : d + 8 ≤ CAN ∨ CAN + 128 ≤ d) (h3 : d + 8 ≤ ACC ∨ ACC + 512 ≤ d)
    (hd : d + 8 ≤ 8192) : word m' base d = word m base d :=
  Mem.readW_congr fun i hi => h _ (by
      simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)

theorem CFrame.whole {base : Addr} {m m' : Mem} (h : CFrame base m m') : Outside base 0 8192 m m' :=
  fun x hx => h x (by simp only [X2, slot] at *; omega) (by simp only [CAN] at *; omega)
    (by simp only [ACC] at *; omega)

/-- A slot other than `X2` is unchanged. -/
theorem CFrame.limbs {base : Addr} {m m' : Mem} (h : CFrame base m m') {i : Fin 22} (hi : i ≠ 1) {j : Nat}
    (hj : j < 16) : limbs m' base (slot i.val) j = limbs m base (slot i.val) j := by
  have := i.isLt
  have hne : i.val ≠ 1 := fun e => hi (Fin.ext e)
  exact congrArg BitVec.toNat (h.word (by simp only [X2, slot]; omega) (by simp only [CAN, slot]; omega)
    (by simp only [ACC, slot]; omega) (by simp only [slot]; omega))

theorem CFrame.E {base : Addr} {m m' : Mem} (h : CFrame base m m') {i : Fin 22} (hi : i ≠ 1) :
    E m' base i = E m base i :=
  congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun j hj => h.limbs hi (by omega))

/-- What a check keeps: the registers but `x20` and `workRegs`, and the memory but `CFrame`'s. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x20 :: workRegs) s t
  mem : CFrame base s.mem t.mem

theorem CKeep.trans {base : Addr} {s t u : State} (h₁ : CKeep base s t) (h₂ : CKeep base t u) :
    CKeep base s u := ⟨h₁.regs.trans h₂.regs, h₁.mem.trans h₂.mem⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem CKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (hk : Keeps rs s t)
    (hr : ∀ r ∈ rs, r ∈ Reg.x20 :: workRegs) (hm : CFrame base s.mem t.mem) : CKeep base s t :=
  ⟨hk.mono hr, hm⟩

/-- `BoundedEnv` after a check: the slots but `X2` are unchanged, and `X2` holds 28-bit limbs. -/
theorem bounded_check {base : Addr} {m m' : Mem} (hb : BoundedEnv m base) (h : CFrame base m m')
    (h2 : VG.Proof.X448.AArch64.Bounded m' base X2) : BoundedEnv m' base := by
  intro i j hj
  by_cases hi : i = 1
  · subst hi; exact bounded_of_legacy h2 j hj
  · rw [show VG.Proof.X448.AArch64.limbs m' base (slot i.val) j = _ from h.limbs hi (by omega)]
    exact hb i j hj

/-! ## Small blocks -/

theorem orBad_ok (s : State) :
    WP isa (.block orBad) s fun t =>
      t.gpr .x20 = s.gpr .x20 ||| s.gpr .x5 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [orBad, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem isZero_val (x : BitVec 64) :
    (0 : BitVec 64) + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ (0 : BitVec 64).toNat + (~~~x).toNat + 1)).toNat =
      if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h]
    have hn : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq e) h
      · exact e
    have hl := x.isLt
    rw [BitVec.toNat_not, decide_eq_false (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)]
    rfl

theorem isZero_ok (s : State) :
    WP isa (.block isZero) s fun t =>
      t.gpr .x5 = (if s.gpr .x5 = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.x5, .x6, .x7] s t := by
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  apply WP.of_runBlock
  simp only [isZero, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    State.addWithCarry, RegUpd.gpr_write, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', e0]
  refine ⟨isZero_val _, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## Comparing slots -/

theorem div_eq_of_add {A B M x y : Nat} (hA : A < M) (hB : B < M) (h : A + M * x = B + M * y) :
    x = y ∧ A = B := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hA
  have hx : (A + M * x) / M = x := by rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hA, Nat.zero_add]
  have hy : (B + M * y) / M = y := by rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hB, Nat.zero_add]
  have exy : x = y := by rw [← hx, ← hy, h]
  subst exy
  exact ⟨rfl, by omega⟩

/-- Limbs below the radix are equal exactly when their values are. -/
theorem valN_inj {f g : Nat → Nat} : ∀ n, (∀ i < n, f i < VG.Proof.X448.radix) →
    (∀ i < n, g i < VG.Proof.X448.radix) → VG.Proof.X448.valN f n = VG.Proof.X448.valN g n →
    ∀ i < n, f i = g i
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hf, hg, h, i, hi => by
    rw [VG.Proof.X448.valN, VG.Proof.X448.valN] at h
    obtain ⟨e1, e2⟩ := div_eq_of_add (VG.Proof.X448.valN_lt fun j hj => hf j (by omega))
      (VG.Proof.X448.valN_lt fun j hj => hg j (by omega)) h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact valN_inj n (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)) e2 i hi
    · exact e1

/-- `canon a`: slot `a` fully reduced into `X2`, as sixteen 28-bit limbs. -/
theorem canon_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a : Fin 22)
    (ha : a ≠ 1) :
    WP isa (.block (canon a.val)) s fun t =>
      VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = (E s.mem base a).val ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  have hal := a.isLt
  have hne : a.val ≠ 1 := fun e => ha (Fin.ext e)
  rw [canon, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (o := X2) (a := slot a.val) (by decide)
    (by simp only [slot]; omega) (by decide) (by simp only [slot]; omega)
    (Or.inr (by simp only [X2, slot]; omega))) fun u ⟨ul, uo, uk⟩ => ?_
  have hsu := hs.of_keeps uk (by decide)
  have ub : VG.Proof.Curve448.AArch64.Bounded u.mem base X2 := fun j hj => by
    rw [show VG.Proof.X448.AArch64.limbs u.mem base X2 j = _ from ul j hj]; exact hb a j hj
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok hsu (o := X2) (by decide) (by decide) ub)
    fun v ⟨vk, vb, vf⟩ => ?_
  have hsv := hsu.of_keeps vk.keeps (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.freeze_ok hsv vb) fun t ⟨tb, tv, tm, tk⟩ => ?_
  refine ⟨tb, ?_, (FieldMem.output uo).trans (vk.mem.trans tm), ((uk.trans vk.keeps).mono
    (fun r hr => List.mem_cons_of_mem _ hr)).trans tk⟩
  have hF : VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = E s.mem base a := by
    have : VG.Proof.X448.AArch64.F v.mem base X2 = VG.Proof.Curve448.AArch64.F u.mem base X2 := vf
    rw [show VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = VG.Proof.X448.AArch64.F v.mem base X2
      from rfl, this]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr ul)
  rw [tv, ← hF, VG.Proof.X448.toFe_val]

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem xor_eq_zero64 (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff

theorem diffStep_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (hn : n < 16) :
    WP isa (.block ([ld .x4 (X2 + 8 * n), ld .x6 (CAN + 8 * n), .logic .eor .x .x4 .x4 .x6,
        .logic .orr .x .x5 .x5 .x4] : List Instr)) s fun t =>
      t.gpr .x5 = s.gpr .x5 ||| (word s.mem base (X2 + 8 * n) ^^^ word s.mem base (CAN + 8 * n)) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  have r1 := hs.read (d := X2 + 8 * n) (n := 8) (by simp only [X2, slot]; omega)
  have r2 := hs.read (d := CAN + 8 * n) (n := 8) (by simp only [CAN]; omega)
  have e1 : (X2 + 8 * n) % 8 = 0 ∧ X2 + 8 * n < 4096 * 8 := by simp only [X2, slot]; omega
  have e2 : (CAN + 8 * n) % 8 = 0 ∧ CAN + 8 * n < 4096 * 8 := by simp only [CAN]; omega
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.read, e1, e2, and_self, BitVec.setWidth_eq, hs.x3, r1, r2,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.reduceMul,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `diffCan`: `x5 = 0` exactly when `X2`'s and `CAN`'s sixteen words are equal. -/
theorem diffCan_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block diffCan) s fun t =>
      (t.gpr .x5 = 0 ↔ ∀ j < 16, word s.mem base (X2 + 8 * j) = word s.mem base (CAN + 8 * j)) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  rw [diffCan, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .x .x5 0 0]) s fun t =>
      t.gpr .x5 = 0 ∧ t.mem = s.mem ∧ Keeps [.x5] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]) fun t0 ⟨z0, m0, k0⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x5 = 0 ↔ ∀ j < n, word s.mem base (X2 + 8 * j) = word s.mem base (CAN + 8 * j)) ∧
      u.mem = s.mem ∧ Keeps [.x4, .x5, .x6] t0 u
  have step : ∀ n u, n < 16 → inv n u →
      WP isa (.block ([ld .x4 (X2 + 8 * n), ld .x6 (CAN + 8 * n), .logic .eor .x .x4 .x4 .x6,
        .logic .orr .x .x5 .x5 .x4] : List Instr)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have hsu : Scr u base := (hs.of_keeps k0 (by decide)).of_keeps uk (by decide)
    refine WP.mono (diffStep_ok hsu hn) fun v ⟨v5, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [v5, or_eq_zero64, uv, xor_eq_zero64, um]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) t0
    ⟨⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => z0⟩, m0, VG.Proof.X448.AArch64.Keeps.refl _ _⟩)
    fun u ⟨uv, um, uk⟩ => ⟨uv, um, (k0.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)).trans uk⟩

/-- `eqSlots a b`: `x20 |= c`, with `c = 0` exactly when slots `a` and `b` hold the same element. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a b : Fin 22)
    (ha : a ≠ 1) (hb1 : b ≠ 1) :
    WP isa (.block (eqSlots a.val b.val)) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ E s.mem base a = E s.mem base b) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      CKeep base s t ∧ BoundedEnv t.mem base := by
  rw [eqSlots]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (canon_ok hs hb a ha) fun u ⟨bu, fu, mu, ku⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  have cu : CKeep base s u := CKeep.of_keeps ku (fun r hr => List.mem_cons_of_mem _ hr) (CFrame.of_field mu)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.copy_ok hsu (o := CAN) (a := X2) (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (by decide)))) fun v ⟨lv, ov, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  have cv : CKeep base u v := CKeep.of_keeps kv (by decide) (CFrame.of_can ov)
  have bu2 : BoundedEnv u.mem base := bounded_check hb cu.mem bu
  have x2v : ∀ j < 16, VG.Proof.X448.AArch64.limbs v.mem base X2 j = VG.Proof.X448.AArch64.limbs u.mem base X2 j :=
    fun j hj => congrArg BitVec.toNat (ov.word (Or.inl (by simp only [X2, slot, CAN]; omega)) (by simp only [X2, slot]; omega))
  have bv2 : VG.Proof.X448.AArch64.Bounded v.mem base X2 := fun j hj => by rw [x2v j hj]; exact bu j hj
  have bv : BoundedEnv v.mem base := bounded_check bu2 cv.mem bv2
  rw [WP.block_append_iff]
  refine WP.mono (canon_ok hsv bv b hb1) fun w ⟨bw, fw, mw, kw⟩ => ?_
  have hsw := hsv.of_keeps kw (by decide)
  have cw : CKeep base v w := CKeep.of_keeps kw (fun r hr => List.mem_cons_of_mem _ hr) (CFrame.of_field mw)
  rw [WP.block_append_iff]
  refine WP.mono (diffCan_ok hsw) fun x ⟨x5, xm, xk⟩ => ?_
  refine WP.mono (orBad_ok x) fun t ⟨t20, tm, tk⟩ => ?_
  have can : ∀ j < 16, word w.mem base (CAN + 8 * j) = word v.mem base (CAN + 8 * j) := fun j hj =>
    Mem.readW_congr fun i hi => mw _ (by
        simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega)]
        simp only [X2, slot, CAN]; omega)
      (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega)]
          simp only [CAN, ACC]; omega)
  have eb : E v.mem base b = E s.mem base b := (cu.trans cv).mem.E hb1
  refine ⟨⟨x.gpr .x5, ?_, ?_⟩, ?_, ?_⟩
  · rw [x5]
    constructor
    · intro h
      apply Fin.ext
      rw [← fu, ← eb, ← fw]
      apply VG.Proof.X448.valN_congr
      intro j hj
      have e := congrArg BitVec.toNat (h j hj)
      rw [can j hj] at e
      have := lv j hj
      change (word v.mem base (CAN + 8 * j)).toNat = VG.Proof.X448.AArch64.limbs u.mem base X2 j at this
      change VG.Proof.X448.AArch64.limbs u.mem base X2 j = (word w.mem base (X2 + 8 * j)).toNat
      rw [← this, e]
    · intro h j hj
      have hv : VG.Proof.X448.AArch64.fe w.mem base X2 = VG.Proof.X448.AArch64.fe u.mem base X2 := by
        rw [fw, eb, fu, ← h]
      have := valN_inj 16 bw bu hv j hj
      apply BitVec.eq_of_toNat_eq
      rw [can j hj]
      change VG.Proof.X448.AArch64.limbs w.mem base X2 j = (word v.mem base (CAN + 8 * j)).toNat
      rw [this]; exact (lv j hj).symm
  · rw [t20, xk.1 _ (by decide), kw.1 _ (by decide), kv.1 _ (by decide), ku.1 _ (by decide)]
  · refine ((cu.trans cv).trans cw).trans ?_
    refine CKeep.of_keeps (rs := [.x4, .x5, .x6, .x20]) ((xk.mono (by decide)).trans (tk.mono (by decide)))
      (by decide) ?_
    rw [tm, xm]; exact CFrame.refl _ _
  · rw [tm, xm]
    exact bounded_check bv cw.mem bw

end VG.Proof.Ed448.AArch64

end
