module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
public import VerifiedGarbage.Impl.AArch64Schedule

/-!
# Keccak-f[1600] on two interleaved states

`vg_keccak_f1600_x2(states = x0, scratch = x1)`. Without FEAT_SHA3, one state
after the other in general registers (`Scalar/Core.lean`): faster than both at
once in base AdvSIMD, whose rotations take two instructions, where a core has
more integer units than vector ones. With it (`sha3`), both at once in the
vector registers (`Sha3/Vector.lean`), in a loop of two rounds whose round
constants (`rcStore`) take the place of the states in memory while they are in
registers.

Some cores run FEAT_SHA3's instructions on one of their two vector units.
Two of the column parities and 8 of the χ steps are computed with base
instructions, and the body's instructions are reordered (`order`, by a list
scheduler over its dependences, for two units with results after two cycles)
so that both units have work at once.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2

open VG.AArch64
open VG.Impl.AArch64Schedule (schedule)

/-- Two rounds, in the order written. -/
def plain : List Instr :=
  Sha3.Vector.round 2 8 0 ++ Sha3.Vector.iota 0 ++ Sha3.Vector.round 2 8 1 ++ Sha3.Vector.iota 1

/-- The order the instructions run in (`schedule`). -/
def order : List Nat :=
  [4, 9, 0, 9, 3, 5, 0, 6, 2, 4, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 14, 13, 13, 15, 3, 12, 2, 12, 1, 10, 0, 9, 2,
    5, 7, 3, 6, 5, 1, 4, 1, 3, 5, 1, 2, 2, 6, 0, 3, 0, 0, 3, 1, 1, 0, 0, 0, 26, 0, 1, 0, 1, 0, 0, 1, 19, 0,
    0, 0, 1, 0, 0, 13, 1, 0, 0, 0, 1, 8, 0, 0, 0, 9, 7, 5, 0, 6, 5, 0, 4, 3, 0, 2, 5, 5, 0, 4, 4, 0, 3, 5,
    0, 0, 0, 9, 8, 8, 10, 8, 5, 9, 3, 7, 5, 6, 1, 5, 2, 3, 1, 2, 0, 1, 3, 0, 0, 0, 4, 0, 1, 3, 0, 0, 0, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]

/-- Two rounds. -/
def body : List Instr := schedule order plain

/-- Both states at once. -/
def vector : Prog isa :=
  .seq (.block (Sha3.Vector.save .x1 0 ++ Pair.load .x0 ++ Sha3.Vector.rcStore .x0 0 ++
    ([.addImm .x .x16 .x0 0, .movz .x .x17 12 0] : List Instr)))
  (.seq (.loop (.block (body ++ ([.addImm .x .x16 .x16 32, .subImm .x .x17 .x17 1] : List Instr))) (.nonzero .x .x17))
    (.block (Pair.store .x0 ++ Sha3.Vector.restore .x1 0)))

open VG.Impl.Sha3.AArch64.Scalar (save restore load store callCore)

/-- One state after the other: `v29` and `v30` hold `states` and `scratch`. -/
def scalar : Prog isa :=
  .seq (.block (save ++ [.vop (.dup .d2 .v29 .x0), .vop (.dup .d2 .v30 .x1), .umov .x .x16 .v29 0] ++ load .x16 16 0 ++
    ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore
  (.seq (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 16 0 ++ load .x16 16 8 ++
    ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 16 8 ++ restore)))))

def code (sha3 : Bool) : Prog isa := if sha3 then vector else scalar

def name (sha3 : Bool) : String := if sha3 then "vg_keccak_f1600_x2_sha3" else "vg_keccak_f1600_x2"

/-- The permutation of the states at `rp`, with its working space at `rb + off`
(128 bytes, and the return address after them). -/
def call (sha3 : Bool) (rp rb : Reg) (off : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x1 rb (off / 2), .addImm .x .x1 .x1 (off - off / 2), .str .x .x30 .x1 128,
    .addImm .x .x0 rp 0])
  (.seq (.call (name sha3) (code sha3)) (.block [.ldr .x .x30 rb (off + 128)]))

/-- The first `n` words of the states at `rp`, to `ra` and to `rb`. -/
def squeeze (n : Nat) (rp ra rb : Reg) : List Instr :=
  (List.range n).flatMap fun i => [.ldr .x .x6 rp (16 * i), .ldr .x .x7 rp (16 * i + 8),
    .str .x .x6 ra (8 * i), .str .x .x7 rb (8 * i)]

end VG.Impl.Sha3.AArch64.Neon.X2
