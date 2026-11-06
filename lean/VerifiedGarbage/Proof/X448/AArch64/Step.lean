module

public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on AArch64: arithmetic steps

Each short instruction block is executed once symbolically. Bounds exclude
overflow before interpreting machine words as natural numbers.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem and28 (x : BitVec 64) : (x &&& 0x0fffffff).toNat = x.toNat % radix := by
  rw [BitVec.toNat_and, show (0x0fffffff : BitVec 64).toNat = 2 ^ 28 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem shr28 (x : BitVec 64) : (x >>> 28).toNat = x.toNat / radix := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- A carry step writes the low 28 bits and retains the high bits in `x6`. -/
theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 8 * i + 8 ≤ 8192) (ha : a + 8 * i + 8 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb : (word s.mem base (a + 8 * i)).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (word s.mem base (a + 8 * i)).toNat + (s.gpr .x6).toNat
    WP isa (.block (carryStep o a i)) s fun s' =>
      (s'.gpr .x6).toNat = v / radix ∧
      s'.mem = s.mem.writeW (off base (o + 8 * i)) (BitVec.ofNat 64 (v % radix)) ∧
      Keeps [.x4, .x6, .x5] s s' := by
  intro v
  have w := hs.write ho
  have l := hs.read ha
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  apply WP.of_runBlock
  simp only [carryStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bytes, Size.bits, addr, ae, oe, State.read, State.load, State.store, hs.x3, hs.mask, l, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write,
    BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    and_self, ite_true, ite_false, reduceCtorEq, Nat.reduceLT, Nat.reduceMul,
    read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  have hv : (word s.mem base (a + 8 * i) + s.gpr .x6).toNat = v := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [shr28, hv]
  · apply congrArg (s.mem.writeW (off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [and28, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % radix) (by
      have := Nat.mod_lt v (show 0 < radix by decide)
      have : radix < 2 ^ 64 := by decide
      omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.X448.AArch64
