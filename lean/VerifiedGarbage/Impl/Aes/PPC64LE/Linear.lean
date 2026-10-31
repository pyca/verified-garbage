module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox

/-! # Shared PPC64LE bit-plane transposes and register helpers

SM4, Camellia and SEED reuse these helpers. AES itself uses the POWER8
vector cryptographic instructions.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- The temporaries. -/
def t0 : Reg := .r22
def t1 : Reg := .r23
def t2 : Reg := .r30

/-- The registers holding masks `1 … 6`. -/
def m : Nat → Reg
  | 1 => .r24 | 2 => .r25 | 3 => .r26 | 4 => .r27 | 5 => .r28 | _ => .r29

def rorI (d n : Reg) (k : Nat) : Instr := .rotr .d d n k
def shrI (d n : Reg) (k : Nat) : Instr := .lsr .d d n k

/-- `d := v`: `lis`, `ori`, `sldi 32`, `oris`, `ori`. The sign extension of
`lis` is shifted out. -/
def imm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- Build masks `k` in registers `m k`. -/
def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm64 (m k) v

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap within `x`: exchanges the bits of `x` in the mask `m k`
with the bits `s` places above them (`t0` is clobbered). -/
def swapIn (x : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 x, andR t0 t0 (m k), xorR x x t0, rorI t0 t0 (64 - s), xorR x x t0]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask `m k` with the bits of `x` `s` places above them. -/
def swapBetween (x y : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 y, andR t0 t0 (m k), xorR y y t0, rorI t0 t0 (64 - s), xorR x x t0]

/-- The masks of the transposes. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- Bytes `0 1 2 3 4 5 6 7` of each word become `0 4 1 5 2 6 3 7`. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 1 16
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 2 8

/-- Interleave the bytes of `q b` and `q (b + 4)`. -/
def swap8 : List Instr := (List.range 4).flatMap fun b => swapBetween (q b) (q (b + 4)) 3 8

/-- BearSSL's `br_aes_ct64_ortho`: transposes the 8×8 bit matrix in each
byte position of the eight words. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 4 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 5 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 6 4)

/-- Shared temporary register used by Camellia. -/
def u7 : Reg := .r24

/-- Shared key pointer used by Camellia. -/
def kp : Reg := .r4

end VG.Impl.Aes.PPC64LE
