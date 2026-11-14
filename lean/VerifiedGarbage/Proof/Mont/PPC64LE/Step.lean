module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Impl.Mont.PPC64LE
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: the arithmetic of a multiply-accumulate step

A step of a row adds the product `x y`, a carry word and a word `t`, the
low word of the product with `addc` into the high word with `addze`, then
the other addend the same way: `x y + t + c ≤ (2⁶⁴ - 1)² + 2 (2⁶⁴ - 1) <
2¹²⁸`, so the carrying adds keep the whole sum (`mac_arith`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem w32_lt (m : Mem) (base : Addr) (d : Nat) : w32 m base d < 2 ^ 32 := BitVec.isLt _

/-- One instruction, then the rest. -/
theorem wp_step {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop} (h : exec i s = some s')
    (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- The arithmetic of a step: the carrying adds keep the whole sum. -/
theorem mac_arith {P t c : Nat} (hP : P ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (ht : t < 2 ^ 64) (hc : c < 2 ^ 64) :
    ((P % 2 ^ 64 + t) % 2 ^ 64 + c) % 2 ^ 64 + 2 ^ 64 * (((P / 2 ^ 64 % 2 ^ 64 +
      (decide (2 ^ 64 ≤ P % 2 ^ 64 + t)).toNat) % 2 ^ 64 +
      (decide (2 ^ 64 ≤ (P % 2 ^ 64 + t) % 2 ^ 64 + c)).toNat) % 2 ^ 64) = P + t + c := by
  obtain ⟨e1, c1⟩ := ca_split (v := P % 2 ^ 64 + t) (by omega_using [ht])
  obtain ⟨e3, c3⟩ := ca_split (v := (P % 2 ^ 64 + t) % 2 ^ 64 + c) (by omega_using [hc])
  generalize (decide (2 ^ 64 ≤ P % 2 ^ 64 + t)).toNat = a at *
  generalize (decide (2 ^ 64 ≤ (P % 2 ^ 64 + t) % 2 ^ 64 + c)).toNat = b at *
  omega_using [hP, ht, hc, e1, e3]

end VG.Proof.Mont.PPC64LE
