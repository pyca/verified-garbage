module

import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! # The invariant of the two-row scan

After the scan has stored `j` words of row `i + 1`'s output, row `i` has
taken `j + 2` words of `b` and `m` and row `i + 1` has taken `j + 1`; row
`i`'s outputs never reach memory, so the invariant states both rows at once:
the stored words times `2⁶⁴` plus the four carries at word `j + 2` are the
old accumulator's first `j + 2` words plus both rows' products so far. The
pointers are at word `p`, `j` or up to two below it inside the loop body, and the
count is the words left after `p`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

/-- The sum of the four carries. -/
abbrev carries (s : State) : Nat :=
  (s.gpr .r7).toNat + (s.gpr .r8).toNat + (s.gpr .r5).toNat + (s.gpr .r11).toNat

structure Inv (s0 : State) (a0 q0 a1 q1 base : BitVec 32) (acc b mod n j p : Nat) (s : State) : Prop where
  index : j + 2 ≤ n
  lag : p ≤ j ∧ j ≤ p + 2
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * p)
  bPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * p)
  mPtr : s.gpr .r4 = base + BitVec.ofNat 32 (mod + 4 * p)
  count : s.gpr .lr = BitVec.ofNat 32 (n - 2 - p)
  scalar0 : s.gpr .r1 = a0
  quotient0 : s.gpr .r2 = q0
  scalar1 : s.gpr .r9 = a1
  quotient1 : s.gpr .r10 = q1
  outside : Outside (State.addr base) acc (4 * j) s0.mem s.mem
  value : 2 ^ 64 * val32 s.mem (State.addr base) acc j + 2 ^ (32 * (j + 2)) * carries s =
    val32 s0.mem (State.addr base) acc (j + 2) +
      a0.toNat * val32 s0.mem (State.addr base) b (j + 2) +
      q0.toNat * val32 s0.mem (State.addr base) mod (j + 2) +
      2 ^ 32 * (a1.toNat * val32 s0.mem (State.addr base) b (j + 1) +
        q1.toNat * val32 s0.mem (State.addr base) mod (j + 1))
  rest : Rest roundClobbers s0 s

end VG.Proof.Bignum.Arm.Fios2
