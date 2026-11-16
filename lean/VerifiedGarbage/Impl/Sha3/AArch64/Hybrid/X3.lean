module

public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2

/-!
# Keccak-f[1600] on three states, as a function (AArch64)

`vg_keccak_f1600_x3_sha3(states, state, scratch)` and `vg_keccak_f1600_x3`
(`Proof/Sha3/X2Contract.lean`; AAPCS64: `states` in `x0`, `state` in `x1`,
`scratch` in `x2`).

`vg_keccak_f1600_x3_sha3` (`vector`) opens a frame
of 128 bytes, in which it keeps the callee-saved general registers
(`[sp, #16]`–`[sp, #104)`), the three pointers (`[sp, #104]`–`[sp, #128)`)
and the scalar round's two temporary lanes (`[sp, #0]`, `[sp, #8]`); keeps
`q8`–`q15` in `scratch`; loads the two interleaved states into `v0`–`v24`
and the third into the general registers (`Scalar.laneReg`); runs the 24
woven rounds (`Hybrid.rounds 0`); and stores the states and restores the
registers.

`vg_keccak_f1600_x3` (`scalar`), which needs no CPU feature, runs the rounds
of `vg_keccak_f1600` on each of the three states in turn, in place, as
`vg_keccak_f1600_x2` does on two (`Neon.X2.scalar`): the callee-saved
registers and the two pointers are kept in vector registers
(`Scalar.Boundary.save`), so it uses neither `scratch` nor the stack.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Hybrid.X3
open VG VG.AArch64

/-- The frame's size. -/
def frameBytes : Nat := 128

/-- The callee-saved general registers, kept at `[sp, #16 + 8 i]`. -/
def savedReg (i : Nat) : Reg := Scalar.Boundary.savedReg i

/-- Save the callee-saved registers and the pointers in the frame, and `q8`–`q15` in `scratch`. -/
def save : List Instr :=
  (List.range 11).map (fun i => .strSp (savedReg i) (16 + 8 * i)) ++
    ([.strSp .x0 104, .strSp .x1 112, .strSp .x2 120] : List Instr) ++
    (List.range 8).map (fun i => .strq (Sha3.Vector.vreg (8 + i)) .x2 (16 * i))

/-- Load the interleaved states into `v0`–`v24` and the third into the general registers. -/
def load : List Instr :=
  Neon.Pair.load .x0 ++ ([.addImm .x .x30 .x1 0] : List Instr) ++
    (List.range 25).map (fun i => .ldr .x (Scalar.laneReg i) .x30 (8 * i))

/-- Store the states, from the pointers kept in the frame. -/
def store : List Instr :=
  ([.ldrSp .x30 112] : List Instr) ++
    (List.range 25).map (fun i => .str .x (Scalar.laneReg i) .x30 (8 * i)) ++
    ([.ldrSp .x0 104] : List Instr) ++ Neon.Pair.store .x0

/-- Restore `q8`–`q15` and the callee-saved registers. -/
def restore : List Instr :=
  ([.ldrSp .x2 120] : List Instr) ++
    (List.range 8).map (fun i => .ldrq (Sha3.Vector.vreg (8 + i)) .x2 (16 * i)) ++
    (List.range 11).map (fun i => .ldrSp (savedReg i) (16 + 8 * i))

/-- The function's body, in its frame. -/
def body : List Instr := save ++ load ++ rounds 0 ++ store ++ restore

/-- With the SHA-3 extension: the interleaved states in vector registers, the
third in general registers beside them. -/
def vector : Prog isa := .frame (.alloc frameBytes) (.block body) (.free frameBytes)

/-- The lanes of the third state, at the pointer `Scalar.Boundary.save` kept
in `v31`, to their registers. -/
def loadThird : List Instr :=
  ([.umov .x .x30 .v31 0] : List Instr) ++
    (List.range 25).map fun i => .ldr .x (Scalar.laneReg i) .x30 (8 * i)

/-- The lanes, from their registers to the third state. -/
def storeThird : List Instr :=
  ([.umov .x .x30 .v31 0] : List Instr) ++
    (List.range 25).map fun i => .str .x (Scalar.laneReg i) .x30 (8 * i)

/-- Without a CPU feature: the scalar rounds on each state in turn, in place. -/
def scalar : Prog isa :=
  .seq (.block (Scalar.Boundary.save ++ ([.addImm .x .x30 .x0 0] : List Instr) ++ Neon.X2.loadLanes 0))
    (.seq (.block Scalar.Lazy.permutationCore)
      (.seq (.block (Neon.X2.storeLanes 0 ++ Neon.X2.loadLanes 1))
        (.seq (.block Scalar.Lazy.permutationCore)
          (.seq (.block (Neon.X2.storeLanes 1 ++ loadThird))
            (.seq (.block Scalar.Lazy.permutationCore)
              (.block (storeThird ++ Scalar.Boundary.restore)))))))

/-- The function's code. -/
def code (sha3 : Bool) : Prog isa := if sha3 then vector else scalar

/-- `vg_keccak_f1600_x3`, and `vg_keccak_f1600_x3_sha3` for the SHA-3 extension. -/
def name (sha3 : Bool) : String :=
  "vg_keccak_f1600_x3" ++ if sha3 then "_sha3" else ""

end VG.Impl.Sha3.AArch64.Hybrid.X3
