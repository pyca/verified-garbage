import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main

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
  · rw [signByte_val]
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
