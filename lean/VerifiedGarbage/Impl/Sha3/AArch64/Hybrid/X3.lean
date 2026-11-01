module

public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary

/-!
# Keccak-f[1600] on three states, as a function (AArch64, SHA-3)

`vg_keccak_f1600_x3_sha3(states, state, scratch)` (`Proof/Sha3/X2Contract.lean`;
AAPCS64: `states` in `x0`, `state` in `x1`, `scratch` in `x2`) opens a frame
of 128 bytes, in which it keeps the callee-saved general registers
(`[sp, #16]`–`[sp, #104)`), the three pointers (`[sp, #104]`–`[sp, #128)`)
and the scalar round's two temporary lanes (`[sp, #0]`, `[sp, #8]`); keeps
`q8`–`q15` in `scratch`; loads the two interleaved states into `v0`–`v24`
and the third into the general registers (`Scalar.laneReg`); runs the 24
woven rounds (`Hybrid.rounds 0`); and stores the states and restores the
registers.
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

/-- The function's code. -/
def code : Prog isa := .frame (.alloc frameBytes) (.block body) (.free frameBytes)

/-- `vg_keccak_f1600_x3_sha3`. -/
def name : String := "vg_keccak_f1600_x3_sha3"

end VG.Impl.Sha3.AArch64.Hybrid.X3
