module
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The table of powers of the windowed ARMv7 exponentiation

`T[j] = x^j R mod M` is array `8 + j` of the workspace, after the RSA
layout's eight. The arithmetic of the layout's arrays leaves them alone: its
`Keeps` covers every byte of the workspace but those of its own arrays and
of its result, all below array 8. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)

/-- The first `k` entries of the table hold `x^j R mod M`, `R = 2^(64 w)`. -/
def TableHolds (m : Mem) (base : BitVec 32) (w M x k : Nat) : Prop :=
  ∀ j < k, numAt m (State.addr base) w (8 + j) < M ∧
    numAt m (State.addr base) w (8 + j) % M = x ^ j * 2 ^ (64 * w) % M

/-- An array after the layout's eight is outside every array an operation of
the layout may write. -/
theorem keeps_table_num {m m' : Mem} {base : Addr} {len w o j : Nat}
    (keep : Keeps base len w o m m') (fits : arrAt w 16 ≤ 8 * len) (ho : o < 8) (hj : j < 8) :
    numAt m' base w (8 + j) = numAt m base w (8 + j) := by
  have bound := Nat.le_trans (array_end_le (w := w) (show 8 + j < 16 by omega)) fits
  unfold numAt
  apply congrArg BitVec.toNat
  apply Mem.read_congr
  intro i hi
  rw [Offset.add_add]
  apply keep (arrAt w (8 + j) + i) (by omega)
  intro a ha
  have below : a < 8 + j := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · simp only [Proof.Rsa.Mont.aAcc]; omega
    · simp only [Proof.Rsa.Mont.aTmp]; omega
    · omega
  have := array_end_le (w := w) below
  omega

theorem TableHolds.of_keeps {m m' : Mem} {base : BitVec 32} {len w M x k o : Nat}
    (h : TableHolds m base w M x k) (keep : Keeps (State.addr base) len w o m m')
    (fits : arrAt w 16 ≤ 8 * len) (ho : o < 8) (hk : k ≤ 8) : TableHolds m' base w M x k := by
  intro j hj
  rw [keeps_table_num keep fits ho (by omega)]
  exact h j hj

theorem TableHolds.of_mem {m m' : Mem} {base : BitVec 32} {w M x k : Nat}
    (h : TableHolds m base w M x k) (mem : m' = m) : TableHolds m' base w M x k := by
  rw [mem]; exact h

/-- A Montgomery product of `x^E R` and `x^d R` is `x^(E + d) R`. -/
theorem mont_mulpow {Y Y' X x E d R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hX : X % m = x ^ d * R % m) (h : Y' * R % m = Y * X % m) : Y' % m = x ^ (E + d) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, hX, ← Nat.mul_mod]
  congr 1
  rw [Nat.pow_add]
  ac_rfl

end VG.Proof.Bignum.Arm
