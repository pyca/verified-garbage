module

public import VerifiedGarbage.Impl.Aes.RISCV64.Linear
public import VerifiedGarbage.Impl.Seed.Layers

/-!
# SEED's G on sixteen words at once, bitsliced, on RISC-V

As on PPC64LE (`Impl/Seed/PPC64LE/G16.lean`): the sixteen 32-bit words of
`G`'s input are the eight 64-bit slots `tSlot i` of the scratch buffer
(`a5`), word `2i + h` in half `h` of slot `i`, and `g16` replaces each with
`G` of it. Both of SEED's S-boxes are affine functions of AES's
(`Proof/Seed/Sbox.lean`), so the code

1. loads the eight words and transposes each byte position's 8×8 bit matrix
   (AES's `ortho`, `Impl/Aes/RISCV64/Linear.lean`): word `j` (in `q j`) then
   holds bit `j` of the 64 bytes, byte `a` of slot `i` at bit `8a + i`;
2. applies `M` to every byte (`mLayer`, from copies of the words in `cp`),
   runs the AES S-box circuit (`Impl/Aes/RISCV64/Sbox.lean`, which spills
   to slots 0–39), and applies `P0` at the bytes `X0` and `X2` of each word
   and `P1` at `X1` and `X3` (`pLayer`, masking with `laneMask0` and
   `laneMask1`);
3. transposes back, and mixes each word's four S-box outputs as `G` does
   (`mixWord`: `Z = ⊕ᵣ rotr₃₂(s, 8r) & Mᵣ`, both halves at once), XORs the
   constant that `0xE7` and `0x2B` contribute to `G` (`gConst`) and stores
   the word back.

RV64I has no rotation: a rotation right by `8r` within each 32-bit half is,
at the bits it does not wrap, the doubleword shifted right by `8r`, and at
those it wraps, the doubleword shifted left by `32 - 8r`; the mask `Mᵣ` is
split between the two (`mixLo`, `mixHi`), which also drops the bits either
shift brings in from the other half. RV64I builds 64-bit constants in
several instructions, so the masks are built once in slots 104–116 of the
scratch buffer (`gKs`, by the functions' setup) and loaded into registers
where they are used, since the S-box overwrites every free register. They
are read through `a3`, which points to slot 104 (`kb`), so that `g16`'s
memory is the slots it writes (0–47, through `a5`) and the masks it only
reads. Only bitwise instructions and shifts by constants touch the data:
no address and no branch depends on it. `g16` writes the S-box's registers
(`q 0 … q 7`, `t0`–`t6`, `a6`, `a7`, `s8`–`s11`), and nothing else.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Impl.Seed

/-! ## Scratch slots (of `a5`) -/

/-- `G`'s input and output words `2i` and `2i + 1`, after the S-box's spill
slots 0–39. -/
def tSlot (i : Nat) : Nat := 40 + i

/-! ## Masks -/

/-- `m` in both 32-bit halves. -/
def both (m : BitVec 32) : BitVec 64 := m ++ m

/-- RFC 4269 §2.2's masks, by index. -/
def gMask : Nat → BitVec 8
  | 0 => 0xFC | 1 => 0xF3 | 2 => 0xCF | _ => 0x3F

/-- `Mᵣ`: byte `j` of the rotation by `8r` is byte `j + r` of the S-box
outputs, which `G` masks with `m_{(2j + r) mod 4}`. -/
def mixMask (r : Nat) : BitVec 32 :=
  gMask ((6 + r) % 4) ++ gMask ((4 + r) % 4) ++ gMask ((2 + r) % 4) ++ gMask (r % 4)

/-- The low `32 - 8r` bits of a 32-bit half. -/
def loBits (r : Nat) : BitVec 32 := BitVec.allOnes 32 >>> (8 * r)

/-- The bit positions of the bytes `X0` and `X2` of each word (`S0`), and of
`X1` and `X3` (`S1`). -/
def laneMask0 : BitVec 64 := 0x00FF00FF00FF00FF
def laneMask1 : BitVec 64 := 0xFF00FF00FF00FF00

/-- The masks of `ortho`, for AES's registers `m 4`, `m 5`, `m 6`. -/
def orthoMasks : List (Nat × BitVec 64) :=
  [(4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- The masks' first slot, and the register pointing to it. -/
def kSlot : Nat := 104
def kb : Reg := .a3

/-- The masks' words from `kb`: `ortho`'s (`m k` in `k - 4`), the lane
masks, and the mixing's (`mixK + j`). -/
def lane0K : Nat := 3
def lane1K : Nat := 4
def mixK : Nat := 5

/-- `d :=` mask word `j`. -/
def ldK (d : Reg) (j : Nat) : Instr := .load .d d kb (8 * j)

/-! ## Registers -/

/-- Where the words are copied for the linear layers. -/
def cp : Nat → Reg
  | 0 => .t1 | 1 => .t2 | 2 => .t3 | 3 => .t4
  | 4 => .t5 | 5 => .t6 | 6 => .a6 | _ => .a7

def lane0 : Reg := .s8
def lane1 : Reg := .s9

/-- The mixing's masks: `M0`, and `Mᵣ` split into the bits that a rotation by
`8r` within a 32-bit half takes from the right shift (`mixLo r`) and those
it takes from the left shift (`mixHi r`); and the constant. -/
def mix0 : Reg := .t2
def mixLo : Nat → Reg
  | 1 => .t3 | 2 => .t4 | _ => .t5
def mixHi : Nat → Reg
  | 1 => .t6 | 2 => .a6 | _ => .a7
def cstR : Reg := .s8

/-- The mixing's masks and constant, as registers and values. -/
def mixMasks : List (Reg × BitVec 64) :=
  [(mix0, both (mixMask 0))] ++
  ((List.range 3).flatMap fun k =>
    [(mixLo (k + 1), both (mixMask (k + 1) &&& loBits (k + 1))),
     (mixHi (k + 1), both (mixMask (k + 1) &&& ~~~loBits (k + 1)))]) ++
  [(cstR, gConst)]

/-- Every mask and its word from `kb`. -/
def gKs : List (Nat × BitVec 64) :=
  orthoMasks.map (fun (k, v) => (k - 4, v)) ++ [(lane0K, laneMask0), (lane1K, laneMask1)] ++
  (List.range mixMasks.length).map fun j => (mixK + j, (mixMasks.getD j (mix0, 0)).2)

/-- Load `ortho`'s masks into `m 4`, `m 5`, `m 6`. -/
def loadOrtho : List Instr := orthoMasks.map fun (k, _) => ldK (m k) (k - 4)

/-- Load the mixing's masks and constant into their registers. -/
def loadMix : List Instr :=
  (List.range mixMasks.length).map fun j => ldK (mixMasks.getD j (mix0, 0)).1 (mixK + j)

/-! ## The layers -/

/-- Copies the eight words to `cp`. -/
def copyQ : List Instr := (List.range 8).map fun j => movR (cp j) (q j)

/-- `q j := ⊕_{i ∈ rows j} x_i`, from the copies. -/
def xorRows (rows : List (List Nat)) : List Instr :=
  copyQ ++ (List.range 8).flatMap fun j =>
    match rows.getD j [] with
    | [] => [xorR (q j) (q j) (q j)]
    | i :: is => movR (q j) (cp i) :: is.map fun i => xorR (q j) (q j) (cp i)

def mLayer : List Instr := xorRows mRows

/-- One term of output word `j` of `pLayer`: input word `i`, at the S-box
lanes whose row of `P0` or `P1` has it. -/
def pTerm (j i : Nat) (first : Bool) : List Instr :=
  let in0 := (p0Rows.getD j []).contains i
  let in1 := (p1Rows.getD j []).contains i
  let mask : Option Reg := if in0 && in1 then none else if in0 then some lane0 else some lane1
  if !(in0 || in1) then []
  else match mask, first with
    | none, true => [movR (q j) (cp i)]
    | none, false => [xorR (q j) (q j) (cp i)]
    | some m, true => [andR (q j) (cp i) m]
    | some m, false => [andR t0 (cp i) m, xorR (q j) (q j) t0]

/-- The input words of output word `j`. -/
def pIns (j : Nat) : List Nat :=
  (List.range 8).filter fun i => (p0Rows.getD j []).contains i || (p1Rows.getD j []).contains i

def pWord (j : Nat) : List Instr :=
  match pIns j with
  | [] => [xorR (q j) (q j) (q j)]
  | i :: is => pTerm j i true ++ is.flatMap fun i => pTerm j i false

def pLayer : List Instr :=
  copyQ ++ [ldK lane0 lane0K, ldK lane1 lane1K] ++ (List.range 8).flatMap pWord

/-- `G`'s mixing of the S-box outputs in `x`, both 32-bit halves at once,
plus `gConst`, stored to `tSlot i` (`t0` and `t1` are clobbered). -/
def mixWord (x : Reg) (i : Nat) : List Instr :=
  [andR t1 x mix0] ++
  ((List.range 3).flatMap fun k =>
    [shrI t0 x (8 * (k + 1)), andR t0 t0 (mixLo (k + 1)), xorR t1 t1 t0,
     shlI t0 x (32 - 8 * (k + 1)), andR t0 t0 (mixHi (k + 1)), xorR t1 t1 t0]) ++
  [xorR t1 t1 cstR, stS (tSlot i) t1]

/-- Loads the eight words, transposed, with `M` applied. -/
def g16In : List Instr :=
  (List.range 8).map (fun i => ldS (q i) (tSlot i)) ++ loadOrtho ++ ortho ++ mLayer

/-- From the S-box's output to the words of `G`. -/
def g16Out : List Instr :=
  pLayer ++ loadOrtho ++ ortho ++ loadMix ++ (List.range 8).flatMap fun i => mixWord (q i) i

/-- `G` of the sixteen words in `tSlot 0 … tSlot 7`, in place. -/
def g16 : List Instr := g16In ++ sboxCode ++ g16Out

end VG.Impl.Seed.RISCV64
