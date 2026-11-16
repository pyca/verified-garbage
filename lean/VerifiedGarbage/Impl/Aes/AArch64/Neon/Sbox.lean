module
public import VerifiedGarbage.Impl.Aes.InvCircuit
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Aes.AArch64.Neon.Alloc
meta import VerifiedGarbage.Impl.Aes.AArch64.Neon.Alloc
public meta import VerifiedGarbage.Impl.Aes.InvCircuit
public meta import VerifiedGarbage.TCB.AArch64.Isa

/-!
# The bitsliced AES S-boxes on AArch64, in AdvSIMD registers

The circuits `Circuit.sbox` and `Circuit.invSbox` on the eight 128-bit words
of the bitsliced state of eight blocks (word `j` holds bit `j` of the 128
bytes): from the words in `v0`–`v7` (`A j`) to `v16`–`v23` (`B j`), with the
temporaries in the registers of both and in `v24`–`v31`, spilling to the
first slots of the scratch buffer at `x5`: the code that `compile` allocates
for them. Their gates are taken in an order (`sboxOrder`, `invSboxOrder`)
that keeps fewer values live than the circuits' own, so that one value is
spilled rather than five or six. The code is written out (and `#guard`
checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64 VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state before the S-box, and of the round's result. -/
def A : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

/-- The registers of the bitsliced state after the S-box. -/
def B : Nat → VReg
  | 0 => .v16 | 1 => .v17 | 2 => .v18 | 3 => .v19 | 4 => .v20 | 5 => .v21 | 6 => .v22 | _ => .v23

/-- The scratch buffer's base. -/
def sb : Reg := .x5

/-- The registers the S-boxes may use for their temporaries, besides those
of their inputs once they are dead: those of their outputs last. -/
def sboxFree : List VReg :=
  [.v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23]

/-- The slots the S-boxes spill to. -/
def spillSlots : List Nat := List.range 6

/-- The circuits' input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × VReg) := (List.range 8).map fun i => (x i, A (7 - i))
def sboxOuts : List (Nat × VReg) := (List.range 8).map fun i => (s i, B (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def veor (d n m : VReg) : Instr := .vop (.logic .eor d n m)
def vand (d n m : VReg) : Instr := .vop (.logic .and d n m)
def vnot (d n : VReg) : Instr := .vop (.not d n)
def vmov (d n : VReg) : Instr := .vop (.mov d n)
def ldS (d : VReg) (k : Nat) : Instr := .ldrq d sb (16 * k)
def stS (k : Nat) (r : VReg) : Instr := .strq r sb (16 * k)

/-- The gates of `Circuit.sbox`, in the order they are compiled in. -/
def sboxOrder : List Gate := [
  xor (t 0) (x 1) (x 2), xor (y 1) (t 0) (x 7), xor (y 14) (x 3) (x 5), xor (y 4) (y 1) (x 3),
  xor (y 9) (x 0) (x 3), xor (y 13) (x 0) (x 6), xor (y 5) (y 1) (x 6), xor (y 8) (x 0) (x 5),
  xor (y 12) (y 13) (y 14), xor (t 1) (x 4) (y 12), xor (y 15) (t 1) (x 5),
  xor (y 20) (t 1) (x 1), and (t 8) (y 5) (y 1), xor (y 6) (y 15) (x 7), xor (y 11) (y 20) (y 9),
  xor (y 2) (y 1) (x 0), xor (y 3) (y 5) (y 8), and (t 3) (y 3) (y 6), and (t 12) (y 9) (y 11),
  xor (y 10) (y 15) (t 0), xor (y 16) (t 0) (y 11), xor (y 18) (x 0) (y 16),
  xor (y 17) (y 10) (y 11), and (t 15) (y 8) (y 10), xor (t 16) (t 15) (t 12),
  xor (y 7) (x 7) (y 11), and (t 13) (y 14) (y 17), xor (t 14) (t 13) (t 12),
  and (t 2) (y 12) (y 15), xor (t 4) (t 3) (t 2), xor (t 17) (t 4) (t 14),
  xor (t 21) (t 17) (y 20), and (t 5) (y 4) (x 7), xor (t 6) (t 5) (t 2), xor (t 18) (t 6) (t 16),
  and (t 7) (y 13) (y 16), xor (t 9) (t 8) (t 7), xor (t 19) (t 9) (t 14),
  xor (y 19) (y 10) (y 8), xor (t 22) (t 18) (y 19), and (t 10) (y 2) (y 7),
  xor (t 11) (t 10) (t 7), xor (t 20) (t 11) (t 16), xor (t 24) (t 20) (y 18),
  xor (y 21) (y 13) (y 16), xor (t 23) (t 19) (y 21), xor (t 25) (t 21) (t 22),
  and (t 26) (t 21) (t 23), xor (t 27) (t 24) (t 26), xor (t 31) (t 22) (t 26),
  and (t 28) (t 25) (t 27), xor (t 29) (t 28) (t 22), and (z 14) (t 29) (y 2),
  and (z 5) (t 29) (y 7), xor (t 30) (t 23) (t 24), and (t 32) (t 31) (t 30),
  xor (t 33) (t 32) (t 24), xor (t 34) (t 23) (t 33), and (z 2) (t 33) (x 7),
  and (z 11) (t 33) (y 4), xor (t 35) (t 27) (t 33), and (t 36) (t 24) (t 35),
  xor (t 37) (t 36) (t 34), xor (t 38) (t 27) (t 36), and (z 1) (t 37) (y 6),
  and (t 39) (t 29) (t 38), xor (t 40) (t 25) (t 39), and (z 4) (t 40) (y 1),
  and (z 13) (t 40) (y 5), xor (t 48) (z 5) (z 13), and (z 10) (t 37) (y 3),
  xor (t 51) (z 2) (z 5), xor (t 47) (z 10) (z 11), xor (t 41) (t 40) (t 37),
  xor (t 44) (t 33) (t 37), xor (t 42) (t 29) (t 33), xor (t 43) (t 29) (t 40),
  and (z 0) (t 44) (y 15), and (z 9) (t 44) (y 12), xor (t 49) (z 9) (z 10),
  and (z 17) (t 41) (y 8), and (z 3) (t 43) (y 16), and (z 12) (t 43) (y 13),
  xor (t 50) (z 2) (z 12), and (z 15) (t 42) (y 9), and (z 6) (t 42) (y 11),
  xor (t 56) (z 12) (t 48), xor (t 45) (t 42) (t 41), and (z 8) (t 41) (y 10),
  xor (t 53) (z 0) (z 3), and (z 7) (t 45) (y 17), and (z 16) (t 45) (y 14),
  xor (t 55) (z 16) (z 17), xor (t 46) (z 15) (z 16), xor (t 52) (z 7) (z 8),
  xor (t 54) (z 6) (z 7), xor (t 59) (z 3) (t 54), xor (t 57) (t 50) (t 53),
  xor (t 61) (z 14) (t 57), xor (t 60) (t 46) (t 57), xnor (s 7) (t 48) (t 60),
  xor (t 58) (z 4) (t 46), xor (t 62) (t 52) (t 58), xor (t 63) (t 49) (t 58),
  xor (t 64) (z 4) (t 59), xor (t 65) (t 61) (t 62), xnor (s 6) (t 56) (t 62),
  xor (t 66) (z 1) (t 63), xor (s 0) (t 59) (t 63), xor (s 3) (t 53) (t 66),
  xor (s 4) (t 51) (t 66), xor (s 5) (t 47) (t 65), xor (t 67) (t 64) (t 65),
  xnor (s 2) (t 55) (t 67), xnor (s 1) (t 64) (s 3)]

/-- The gates of `Circuit.invSbox`, in the order they are compiled in. -/
def invSboxOrder : List Gate := [
  xnor (y 19) (x 4) (x 7), xor (w 0) (x 0) (x 5), xor (y 3) (x 0) (x 3), xnor (y 6) (x 1) (y 3),
  xor (y 14) (x 4) (y 6), xor (y 9) (x 3) (x 4), xnor (y 18) (x 2) (y 9), xor (y 8) (x 3) (y 6),
  xor (y 1) (x 3) (y 19), xnor (y 13) (x 6) (y 1), and (t 3) (y 3) (y 6), xor (y 5) (y 3) (y 8),
  and (t 8) (y 5) (y 1), xor (y 10) (y 8) (y 19), xor (y 12) (y 14) (y 13),
  xor (y 2) (y 5) (y 13), xor (y 4) (y 3) (y 12), xor (y 11) (y 4) (w 0), and (t 15) (y 8) (y 10),
  xor (y 17) (y 10) (y 11), xor (y 7) (y 18) (y 2), and (t 10) (y 2) (y 7),
  and (t 13) (y 14) (y 17), xor (y 16) (y 1) (y 7), xor (y 21) (y 13) (y 16),
  and (t 7) (y 13) (y 16), xor (t 9) (t 8) (t 7), xor (t 11) (t 10) (t 7),
  and (t 12) (y 9) (y 11), xor (t 14) (t 13) (t 12), xor (t 16) (t 15) (t 12),
  xor (t 19) (t 9) (t 14), xor (t 23) (t 19) (y 21), xor (t 20) (t 11) (t 16),
  xor (t 24) (t 20) (y 18), xor (y 20) (y 9) (y 11), xor (y 15) (y 16) (y 17),
  and (t 2) (y 12) (y 15), xor (t 4) (t 3) (t 2), xor (t 17) (t 4) (t 14),
  xor (t 21) (t 17) (y 20), xor (y 0) (y 7) (y 11), and (t 5) (y 4) (y 0), xor (t 6) (t 5) (t 2),
  xor (t 18) (t 6) (t 16), xor (t 22) (t 18) (y 19), xor (t 30) (t 23) (t 24),
  xor (t 25) (t 21) (t 22), and (t 26) (t 21) (t 23), xor (t 27) (t 24) (t 26),
  xor (t 31) (t 22) (t 26), and (t 32) (t 31) (t 30), xor (t 33) (t 32) (t 24),
  and (z 11) (t 33) (y 4), and (z 2) (t 33) (y 0), xor (t 34) (t 23) (t 33),
  and (t 28) (t 25) (t 27), xor (t 29) (t 28) (t 22), and (z 5) (t 29) (y 7),
  and (z 14) (t 29) (y 2), xor (t 35) (t 27) (t 33), and (t 36) (t 24) (t 35),
  xor (t 37) (t 36) (t 34), xor (t 38) (t 27) (t 36), and (t 39) (t 29) (t 38),
  xor (t 40) (t 25) (t 39), and (z 1) (t 37) (y 6), and (z 10) (t 37) (y 3),
  and (z 4) (t 40) (y 1), and (z 13) (t 40) (y 5), xor (w 9) (z 2) (z 10),
  xor (t 41) (t 40) (t 37), and (z 8) (t 41) (y 10), xor (t 43) (t 29) (t 40),
  and (z 12) (t 43) (y 13), and (z 3) (t 43) (y 16), and (z 17) (t 41) (y 8),
  xor (t 44) (t 33) (t 37), xor (t 42) (t 29) (t 33), and (z 15) (t 42) (y 9),
  and (z 0) (t 44) (y 15), and (z 9) (t 44) (y 12), xor (t 45) (t 42) (t 41),
  and (z 6) (t 42) (y 11), xor (w 11) (z 9) (z 17), and (z 7) (t 45) (y 17),
  and (z 16) (t 45) (y 14), xor (w 16) (z 11) (w 11), xor (w 1) (z 6) (z 15),
  xor (w 2) (z 12) (w 1), xor (w 3) (z 13) (w 2), xor (w 4) (z 16) (w 3), xor (w 5) (z 8) (w 4),
  xor (w 20) (z 9) (w 9), xor (w 6) (z 3) (w 5), xor (w 10) (z 0) (w 5), xor (s 0) (z 5) (w 6),
  xor (w 7) (z 4) (w 6), xor (s 3) (z 2) (w 10), xor (w 14) (z 7) (w 7), xor (w 8) (z 1) (w 7),
  xor (s 6) (z 8) (w 14), xor (w 15) (s 0) (w 10), xor (w 12) (w 8) (w 9),
  xor (w 13) (z 14) (w 12), xor (w 17) (z 11) (w 13), xor (s 5) (w 8) (w 15),
  xor (s 7) (z 15) (w 16), xor (w 18) (z 16) (w 16), xor (w 19) (z 12) (w 17),
  xor (s 2) (z 13) (w 17), xor (s 1) (w 18) (w 19), xor (w 21) (s 6) (w 18),
  xor (w 22) (w 15) (w 21), xor (s 4) (w 20) (w 22)]

#guard sboxOrder.length == sbox.length && sboxOrder.all (sbox.contains ·)
#guard invSboxOrder.length == invSbox.length && invSboxOrder.all (invSbox.contains ·)

/-- The S-box: from the state in `A 0 … A 7` to `B 0 … B 7`. -/
def sboxCode : List Instr := [
  veor .v5 .v6 .v5, veor .v24 .v5 .v0, veor .v25 .v4 .v2, veor .v26 .v24 .v4, veor .v4 .v7 .v4,
  veor .v27 .v7 .v1, veor .v1 .v24 .v1, veor .v28 .v7 .v2, veor .v29 .v27 .v25, veor .v3 .v3 .v29,
  veor .v2 .v3 .v2, veor .v3 .v3 .v6, vand .v6 .v1 .v24, veor .v30 .v2 .v0, veor .v31 .v3 .v4,
  veor .v16 .v24 .v7, veor .v17 .v1 .v28, vand .v18 .v17 .v30, vand .v19 .v4 .v31,
  veor .v20 .v2 .v5, veor .v5 .v5 .v31, veor .v7 .v7 .v5, veor .v21 .v20 .v31,
  vand .v22 .v28 .v20, veor .v22 .v22 .v19, veor .v23 .v0 .v31, stS 0 .v31, vand .v31 .v25 .v21,
  veor .v31 .v31 .v19, vand .v19 .v29 .v2, veor .v18 .v18 .v19, veor .v18 .v18 .v31,
  veor .v18 .v18 .v3, vand .v3 .v26 .v0, veor .v3 .v3 .v19, veor .v3 .v3 .v22, vand .v19 .v27 .v5,
  veor .v6 .v6 .v19, veor .v6 .v6 .v31, veor .v31 .v20 .v28, veor .v3 .v3 .v31,
  vand .v31 .v16 .v23, veor .v31 .v31 .v19, veor .v31 .v31 .v22, veor .v31 .v31 .v7,
  veor .v7 .v27 .v5, veor .v6 .v6 .v7, veor .v7 .v18 .v3, vand .v18 .v18 .v6, veor .v22 .v31 .v18,
  veor .v18 .v3 .v18, vand .v19 .v7 .v22, veor .v19 .v19 .v3, vand .v16 .v19 .v16,
  vand .v23 .v19 .v23, veor .v3 .v6 .v31, vand .v18 .v18 .v3, veor .v18 .v18 .v31,
  veor .v6 .v6 .v18, vand .v0 .v18 .v0, vand .v26 .v18 .v26, veor .v3 .v22 .v18,
  vand .v31 .v31 .v3, veor .v6 .v31 .v6, veor .v22 .v22 .v31, vand .v30 .v6 .v30,
  vand .v22 .v19 .v22, veor .v7 .v7 .v22, vand .v24 .v7 .v24, vand .v1 .v7 .v1, veor .v1 .v23 .v1,
  vand .v17 .v6 .v17, veor .v23 .v0 .v23, veor .v26 .v17 .v26, veor .v22 .v7 .v6,
  veor .v6 .v18 .v6, veor .v18 .v19 .v18, veor .v19 .v19 .v7, vand .v2 .v6 .v2, vand .v6 .v6 .v29,
  veor .v6 .v6 .v17, vand .v28 .v22 .v28, vand .v5 .v19 .v5, vand .v19 .v19 .v27,
  veor .v0 .v0 .v19, vand .v4 .v18 .v4, ldS .v27 0, vand .v27 .v18 .v27, veor .v19 .v19 .v1,
  veor .v18 .v18 .v22, vand .v22 .v22 .v20, veor .v2 .v2 .v5, vand .v21 .v18 .v21,
  vand .v18 .v18 .v25, veor .v28 .v18 .v28, veor .v4 .v4 .v18, veor .v22 .v21 .v22,
  veor .v27 .v27 .v21, veor .v5 .v5 .v27, veor .v0 .v0 .v2, veor .v16 .v16 .v0, veor .v0 .v4 .v0,
  veor .v1 .v1 .v0, vnot .v1 .v1, veor .v4 .v24 .v4, veor .v22 .v22 .v4, veor .v6 .v6 .v4,
  veor .v24 .v24 .v5, veor .v16 .v16 .v22, veor .v17 .v19 .v22, vnot .v17 .v17,
  veor .v30 .v30 .v6, veor .v5 .v5 .v6, veor .v20 .v2 .v30, veor .v19 .v23 .v30,
  veor .v18 .v26 .v16, veor .v16 .v24 .v16, veor .v21 .v28 .v16, vnot .v21 .v21,
  veor .v22 .v24 .v20, vnot .v22 .v22, vmov .v23 .v5, vmov .v16 .v1]

/-- The inverse S-box: from the state in `A 0 … A 7` to `B 0 … B 7`. -/
def invSboxCode : List Instr := [
  veor .v0 .v3 .v0, vnot .v0 .v0, veor .v2 .v7 .v2, veor .v7 .v7 .v4, veor .v6 .v6 .v7,
  vnot .v6 .v6, veor .v24 .v3 .v6, veor .v3 .v4 .v3, veor .v5 .v5 .v3, vnot .v5 .v5,
  veor .v25 .v4 .v6, veor .v4 .v4 .v0, veor .v1 .v1 .v4, vnot .v1 .v1, vand .v26 .v7 .v6,
  veor .v27 .v7 .v25, vand .v28 .v27 .v4, veor .v29 .v25 .v0, veor .v30 .v24 .v1,
  veor .v31 .v27 .v1, veor .v16 .v7 .v30, veor .v2 .v16 .v2, vand .v17 .v25 .v29,
  veor .v18 .v29 .v2, veor .v19 .v5 .v31, vand .v20 .v31 .v19, vand .v21 .v24 .v18,
  veor .v22 .v4 .v19, veor .v23 .v1 .v22, stS 0 .v24, vand .v24 .v1 .v22, veor .v28 .v28 .v24,
  veor .v20 .v20 .v24, vand .v24 .v3 .v2, veor .v21 .v21 .v24, veor .v17 .v17 .v24,
  veor .v28 .v28 .v21, veor .v28 .v28 .v23, veor .v20 .v20 .v17, veor .v20 .v20 .v5,
  veor .v5 .v3 .v2, veor .v23 .v22 .v18, vand .v24 .v30 .v23, veor .v26 .v26 .v24,
  veor .v26 .v26 .v21, veor .v26 .v26 .v5, veor .v5 .v19 .v2, vand .v21 .v16 .v5,
  veor .v21 .v21 .v24, veor .v21 .v21 .v17, veor .v21 .v21 .v0, veor .v0 .v28 .v20,
  veor .v17 .v26 .v21, vand .v26 .v26 .v28, veor .v24 .v20 .v26, veor .v26 .v21 .v26,
  vand .v26 .v26 .v0, veor .v26 .v26 .v20, vand .v16 .v26 .v16, vand .v5 .v26 .v5,
  veor .v28 .v28 .v26, vand .v0 .v17 .v24, veor .v0 .v0 .v21, vand .v19 .v0 .v19,
  vand .v31 .v0 .v31, veor .v21 .v24 .v26, vand .v20 .v20 .v21, veor .v28 .v20 .v28,
  veor .v24 .v24 .v20, vand .v24 .v0 .v24, veor .v17 .v17 .v24, vand .v6 .v28 .v6,
  vand .v7 .v28 .v7, vand .v4 .v17 .v4, vand .v27 .v17 .v27, veor .v7 .v5 .v7,
  veor .v24 .v17 .v28, vand .v29 .v24 .v29, veor .v17 .v0 .v17, vand .v1 .v17 .v1,
  vand .v17 .v17 .v22, vand .v25 .v24 .v25, veor .v28 .v26 .v28, veor .v0 .v0 .v26,
  vand .v3 .v0 .v3, vand .v23 .v28 .v23, vand .v28 .v28 .v30, veor .v24 .v0 .v24,
  vand .v0 .v0 .v2, veor .v25 .v28 .v25, vand .v18 .v24 .v18, ldS .v2 0, vand .v24 .v24 .v2,
  veor .v25 .v16 .v25, veor .v0 .v0 .v3, veor .v0 .v1 .v0, veor .v0 .v27 .v0, veor .v0 .v24 .v0,
  veor .v0 .v29 .v0, veor .v28 .v28 .v7, veor .v17 .v17 .v0, veor .v23 .v23 .v0,
  veor .v19 .v19 .v17, veor .v4 .v4 .v17, veor .v20 .v5 .v23, veor .v18 .v18 .v4,
  veor .v6 .v6 .v4, veor .v17 .v29 .v18, veor .v23 .v19 .v23, veor .v7 .v6 .v7,
  veor .v31 .v31 .v7, veor .v16 .v16 .v31, veor .v18 .v6 .v23, veor .v3 .v3 .v25,
  veor .v24 .v24 .v25, veor .v1 .v1 .v16, veor .v21 .v27 .v16, veor .v22 .v24 .v1,
  veor .v24 .v17 .v24, veor .v23 .v23 .v24, veor .v28 .v28 .v23, vmov .v23 .v19, vmov .v19 .v28,
  vmov .v16 .v3]

#guard sboxCode == compile sb sboxOrder sboxIns sboxOuts sboxFree spillSlots
#guard invSboxCode == compile sb invSboxOrder sboxIns sboxOuts sboxFree spillSlots

end VG.Impl.Aes.AArch64.Neon
