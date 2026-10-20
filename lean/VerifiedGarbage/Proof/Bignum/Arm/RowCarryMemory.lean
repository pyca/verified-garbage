module

public import VerifiedGarbage.Proof.Mont.Words32
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.TCB.Arm.Isa

/-! # Integrate the two top-word stores into a full accumulator value -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem rowCarry_memory {s t : State} {base : Addr} {size o n : Nat}
    (hn : base.toNat + size ≤ 2 ^ 32) (ho : o + 4 * (n + 2) ≤ size)
    (hm : t.mem = (s.mem.writeW (off base (o + 4 * n)) (t.gpr .r3)).writeW
      (off base (o + 4 * n + 4)) (t.gpr .r4)) :
    Outside base (o + 4 * n) 8 s.mem t.mem ∧
      val32 t.mem base o (n + 2) = val32 s.mem base o n +
        2 ^ (32 * n) * ((t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r4).toNat) := by
  have k1 := writeW32_outside s.mem base (d := o + 4 * n) (t.gpr .r3) (by omega)
  have k2 := writeW32_outside (s.mem.writeW (off base (o + 4 * n)) (t.gpr .r3))
    base (d := o + 4 * n + 4) (t.gpr .r4) (by omega)
  rw [← hm] at k2
  have outside : Outside base (o + 4 * n) 8 s.mem t.mem :=
    (k1.mono (by omega) (by omega)).trans (k2.mono (by omega) (by omega))
  have low := outside.val32 (d := o) (k := n) (by omega) (by omega)
  have top0 : w32 t.mem base (o + 4 * n) = (t.gpr .r3).toNat := by
    rw [hm, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self]
  have top1 : w32 t.mem base (o + 4 * n + 4) = (t.gpr .r4).toNat := by
    rw [hm, w32_write_self]
  refine ⟨outside, ?_⟩
  rw [val32_append t.mem base o n 2]
  rw [low, val32, val32, val32, top0, top1, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum.Arm
