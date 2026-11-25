module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# The bitsliced AES S-boxes in AdvSIMD registers

The state's slices are in `A j` (`v0`–`v7`) before SubBytes and in `B j`
(`v16`–`v23`) after it. The circuits are `Circuit.sbox` and its inverse
without their constants (`subBytes` is the S-box less `{63}`, `invSubBytes`
the inverse S-box of its input plus `{63}`), their gates in an order with
few values alive at once: one value is spilled, to slot 0 of the scratch
buffer. No register among `v8`–`v15`, whose low halves a function must
preserve, is written.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64

/-- The scratch buffer's base. -/
def sb : Reg := .x5

/-- The slices before SubBytes, and the blocks a batch starts from. -/
def A : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
  | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

/-- The slices after SubBytes, and the blocks a batch ends with. -/
def B : Nat → VReg
  | 0 => .v16 | 1 => .v17 | 2 => .v18 | 3 => .v19
  | 4 => .v20 | 5 => .v21 | 6 => .v22 | _ => .v23

def veor (d n m : VReg) : Instr := .vop (.logic .eor d n m)
def vand (d n m : VReg) : Instr := .vop (.logic .and d n m)

/-! Short forms for the circuits. -/

def vx (d n m : VReg) : Instr := veor d n m
def va (d n m : VReg) : Instr := vand d n m
def sv (k : Nat) (r : VReg) : Instr := .strq r sb (16 * k)
def ld (r : VReg) (k : Nat) : Instr := .ldrq r sb (16 * k)

/-- `Circuit.sbox` without its constant, from `A j` to `B j`. -/
def subBytes : List Instr := [
  vx .v27 .v5 .v2, vx .v26 .v27 .v1, vx .v28 .v26 .v6, vx .v31 .v28 .v3, vx .v30 .v31 .v7,
  vx .v31 .v26 .v0, vx .v3 .v30 .v27, vx .v24 .v3 .v31, vx .v25 .v24 .v4, vx .v5 .v24 .v5,
  vx .v2 .v5 .v7, vx .v29 .v3 .v4, vx .v0 .v30 .v4, va .v4 .v2 .v28, vx .v23 .v25 .v2,
  vx .v19 .v31 .v7, vx .v30 .v25 .v30, vx .v1 .v29 .v1, vx .v22 .v24 .v28, va .v17 .v29 .v30,
  va .v21 .v23 .v22, vx .v4 .v17 .v4, vx .v16 .v17 .v21, va .v20 .v19 .v1, vx .v18 .v16 .v20,
  va .v21 .v25 .v24, vx .v17 .v18 .v21, vx .v27 .v17 .v27, va .v18 .v7 .v26, vx .v21 .v21 .v18,
  vx .v21 .v21 .v4, vx .v17 .v2 .v6, vx .v17 .v21 .v17, vx .v20 .v29 .v5, vx .v21 .v22 .v1,
  va .v18 .v20 .v21, vx .v18 .v16 .v18, va .v16 .v31 .v0, vx .v18 .v18 .v16, vx .v3 .v18 .v3,
  vx .v4 .v4 .v16, va .v16 .v5 .v6, vx .v4 .v4 .v16, vx .v16 .v5 .v26, vx .v4 .v4 .v16,
  vx .v16 .v17 .v4, va .v17 .v17 .v27, vx .v18 .v27 .v3, sv 0 .v6, vx .v6 .v4 .v17,
  va .v6 .v6 .v18, vx .v17 .v3 .v17, vx .v6 .v3 .v6, vx .v27 .v27 .v6, vx .v18 .v17 .v6,
  va .v3 .v3 .v18, vx .v27 .v3 .v27, vx .v3 .v17 .v3, va .v18 .v16 .v17, vx .v4 .v4 .v18,
  va .v3 .v4 .v3, vx .v3 .v3 .v16, va .v1 .v4 .v1, va .v16 .v3 .v22, vx .v1 .v16 .v1,
  vx .v18 .v4 .v3, va .v17 .v18 .v20, va .v22 .v18 .v21, vx .v18 .v22 .v16, va .v22 .v4 .v19,
  vx .v4 .v4 .v6, va .v20 .v3 .v23, vx .v3 .v3 .v27, va .v2 .v27 .v2, va .v28 .v27 .v28,
  va .v24 .v3 .v24, va .v0 .v4 .v0, vx .v27 .v6 .v27, va .v31 .v4 .v31, vx .v4 .v4 .v3,
  vx .v31 .v31 .v17, va .v26 .v6 .v26, vx .v28 .v28 .v26, vx .v1 .v1 .v28, va .v25 .v3 .v25,
  va .v30 .v4 .v30, va .v6 .v6 .v7, va .v4 .v4 .v29, vx .v7 .v4 .v20, vx .v4 .v6 .v17,
  vx .v3 .v31 .v7, vx .v25 .v7 .v25, va .v7 .v27 .v5, vx .v17 .v25 .v22, vx .v16 .v3 .v1,
  vx .v21 .v1 .v17, vx .v5 .v16 .v22, vx .v31 .v18 .v30, vx .v4 .v4 .v25, ld .v25 0,
  va .v27 .v27 .v25, vx .v30 .v17 .v30, vx .v25 .v30 .v28, vx .v2 .v5 .v2, vx .v5 .v18 .v0,
  vx .v31 .v31 .v26, vx .v18 .v4 .v7, vx .v23 .v25 .v24, vx .v25 .v30 .v18, vx .v3 .v2 .v20,
  vx .v27 .v31 .v27, vx .v20 .v3 .v6, vx .v22 .v25 .v5, vx .v19 .v27 .v24]

/-- The inverse S-box's circuit, of an input with `{63}` added, from `A j`
to `B j`. -/
def invSubBytes : List Instr := [
  vx .v25 .v7 .v6, vx .v28 .v5 .v4, vx .v27 .v4 .v2, vx .v24 .v28 .v1, vx .v26 .v27 .v0,
  vx .v30 .v25 .v26, vx .v25 .v25 .v0, vx .v0 .v24 .v6, vx .v1 .v0 .v5, vx .v6 .v24 .v3,
  vx .v29 .v24 .v2, vx .v3 .v25 .v4, va .v5 .v1 .v25, va .v31 .v6 .v0, vx .v4 .v29 .v7,
  vx .v17 .v6 .v1, vx .v5 .v5 .v31, vx .v7 .v17 .v7, vx .v22 .v6 .v3, vx .v21 .v7 .v30,
  vx .v16 .v4 .v22, va .v23 .v16 .v30, vx .v24 .v21 .v24, va .v18 .v4 .v21, vx .v20 .v5 .v23,
  vx .v20 .v20 .v18, vx .v2 .v20 .v2, vx .v18 .v0 .v25, va .v19 .v17 .v18, vx .v31 .v19 .v31,
  va .v19 .v22 .v7, vx .v20 .v31 .v19, vx .v19 .v20 .v23, vx .v19 .v19 .v29, vx .v29 .v7 .v29,
  va .v20 .v24 .v27, vx .v31 .v31 .v20, vx .v23 .v7 .v0, sv 0 .v18, va .v18 .v3 .v23,
  vx .v31 .v31 .v18, vx .v28 .v31 .v28, vx .v31 .v23 .v27, va .v18 .v29 .v31, vx .v5 .v5 .v18,
  vx .v5 .v5 .v20, vx .v26 .v5 .v26, va .v5 .v26 .v2, vx .v26 .v26 .v28, vx .v20 .v19 .v5,
  vx .v5 .v28 .v5, vx .v18 .v2 .v19, va .v5 .v5 .v18, vx .v5 .v19 .v5, vx .v18 .v20 .v5,
  va .v18 .v19 .v18, vx .v2 .v2 .v5, vx .v2 .v18 .v2, vx .v19 .v20 .v18, va .v18 .v26 .v20,
  vx .v28 .v28 .v18, va .v19 .v28 .v19, vx .v26 .v19 .v26, va .v3 .v2 .v3, va .v7 .v26 .v7,
  va .v22 .v26 .v22, va .v23 .v2 .v23, vx .v18 .v26 .v28, va .v20 .v18 .v21, va .v4 .v18 .v4,
  vx .v26 .v2 .v26, vx .v2 .v2 .v5, va .v31 .v2 .v31, va .v29 .v2 .v29, va .v2 .v28 .v16,
  va .v0 .v26 .v0, va .v30 .v28 .v30, va .v6 .v26 .v6, va .v27 .v5 .v27, va .v24 .v5 .v24,
  vx .v5 .v5 .v28, va .v28 .v5 .v25, va .v1 .v5 .v1, vx .v25 .v30 .v23, vx .v1 .v1 .v29,
  vx .v27 .v27 .v22, vx .v25 .v27 .v25, vx .v27 .v1 .v6, vx .v0 .v0 .v20, vx .v25 .v25 .v7,
  vx .v2 .v25 .v2, vx .v5 .v26 .v5, va .v1 .v5 .v17, vx .v26 .v2 .v3, ld .v19 0, va .v5 .v5 .v19,
  vx .v19 .v27 .v24, vx .v16 .v26 .v24, vx .v24 .v16 .v28, vx .v28 .v24 .v5, vx .v26 .v29 .v3,
  vx .v3 .v1 .v6, vx .v1 .v26 .v4, vx .v18 .v1 .v25, vx .v21 .v3 .v2, vx .v2 .v24 .v30,
  vx .v4 .v19 .v31, vx .v24 .v2 .v0, vx .v26 .v1 .v22, vx .v30 .v28 .v23, vx .v31 .v28 .v7,
  vx .v20 .v31 .v20, vx .v22 .v30 .v4, vx .v23 .v26 .v24, vx .v17 .v24 .v22]

end VG.Impl.Aes.AArch64.Neon
