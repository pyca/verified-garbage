module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy

/-!
# Keccak-f[1600] on two interleaved states, as a function (AArch64)

`vg_keccak_f1600_x2(states, scratch)` and `vg_keccak_f1600_x2_sha3`
(`Proof/Sha3/X2Contract.lean`; AAPCS64: `states` in `x0`, `scratch` in `x1`).

`vg_keccak_f1600_x2_sha3` (`vector`) runs the two-lane rounds that the paired
SHAKE samplers inlined (`Pair.roundsProg`, the SHA-3 extension's
instructions): `q8`–`q15` saved in `scratch`, both states loaded into
`v0`–`v24`, the 24 rounds, the states stored and `q8`–`q15` restored. Only
`x16` and the vector registers change.

`vg_keccak_f1600_x2` (`scalar`), which needs no CPU feature, runs the rounds
of `vg_keccak_f1600` (`Scalar.Lazy.permutationCore`, the 25 lanes in general
registers) on each state in turn, in place: lane `i` of state `k` is loaded
from and stored to `[states + 16 i + 8 k]`. As there, the callee-saved
general registers and the pointer are kept in vector registers
(`Scalar.Boundary.save`), so it uses neither `scratch` nor the stack; it
changes `x0`–`x17`.

A caller (`call`) passes the states' pointer and the function's working
space, keeps its return address next to that working space, and squeezes the
output from memory (`squeeze`).
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2

open VG VG.AArch64

/-- With the SHA-3 extension: both states in vector registers. -/
def vector : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Sha3.Vector.save ++ Pair.load .x0))
    (.seq (Pair.roundsProg 24)
      (.block (Pair.store .x0 ++ VG.Impl.Sha3.AArch64.Sha3.Vector.restore)))

/-- The lanes of state `k` of the two at `x30`, to their registers. -/
def loadLanes (k : Nat) : List Instr :=
  (List.range 25).map fun i => .ldr .x (Scalar.laneReg i) .x30 (16 * i + 8 * k)

/-- The lanes, from their registers to state `k` of the two at the pointer
`Scalar.Boundary.save` kept in `v30`. -/
def storeLanes (k : Nat) : List Instr :=
  ([.umov .x .x30 .v30 0] : List Instr) ++
    (List.range 25).map fun i => .str .x (Scalar.laneReg i) .x30 (16 * i + 8 * k)

/-- Without a CPU feature: the scalar rounds on each state in turn, in place. -/
def scalar : Prog isa :=
  .seq (.block (Scalar.Boundary.save ++ ([.addImm .x .x30 .x0 0] : List Instr) ++ loadLanes 0))
    (.seq (.block Scalar.Lazy.permutationCore)
      (.seq (.block (storeLanes 0 ++ loadLanes 1))
        (.seq (.block Scalar.Lazy.permutationCore)
          (.block (storeLanes 1 ++ Scalar.Boundary.restore)))))

/-- The function's code. -/
def code (sha3 : Bool) : Prog isa := if sha3 then vector else scalar

/-- `vg_keccak_f1600_x2`, and `vg_keccak_f1600_x2_sha3` for the SHA-3 extension. -/
def name (sha3 : Bool) : String :=
  "vg_keccak_f1600_x2" ++ if sha3 then "_sha3" else ""

/-- A call on the states at `p`, with the function's working space at
`base + off` (`off` below 8190, in two immediates), and the caller's return
address kept in the 8 bytes after it. `vg_keccak_f1600_x2_sha3` writes only
`x16`, `x17`, `x30` and vector registers, so `x1` still points there after
it; `vg_keccak_f1600_x2` keeps only the callee-saved registers, one of which
`base` is. -/
def call (sha3 : Bool) (p base : Reg) (off : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x1 base (off / 2), .addImm .x .x1 .x1 (off - off / 2),
      .str .x .x30 .x1 128, .addImm .x .x0 p 0])
    (.seq (.call (name sha3) (code sha3))
      (.block [if sha3 then .ldr .x .x30 .x1 128 else .ldr .x .x30 base (off + 128)]))

/-- The first `words` words of each of the states at `p`, to `a` and `b`. -/
def squeeze (words : Nat) (p a b : Reg) : List Instr :=
  (List.range words).flatMap fun i =>
    [.ldr .x .x6 p (16*i), .ldr .x .x7 p (16*i+8), .str .x .x6 a (8*i), .str .x .x7 b (8*i)]

end VG.Impl.Sha3.AArch64.Neon.X2
