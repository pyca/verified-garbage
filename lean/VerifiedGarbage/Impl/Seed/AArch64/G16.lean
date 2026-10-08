import VerifiedGarbage.Impl.Aes.AArch64.Linear
import VerifiedGarbage.Impl.Seed.Layers

/-!
# SEED's G on sixteen words at once, bitsliced, on AArch64

As on x86-64 (`Impl/Seed/X86_64/G16.lean`): the sixteen 32-bit words of
`G`'s input are the eight 64-bit slots `tSlot i` of the scratch buffer
(`x5`), word `2i + h` in half `h` of slot `i`, and `g16` replaces each with
`G` of it. Both of SEED's S-boxes are affine functions of AES's
(`Proof/Seed/Sbox.lean`), so the code

1. loads the eight words and transposes each byte position's 8×8 bit matrix
   (AES's `ortho`, `Impl/Aes/AArch64/Linear.lean`): word `j` (in `q j`) then
   holds bit `j` of the 64 bytes, byte `a` of slot `i` at bit `8a + i`;
2. applies `M` to every byte (`mLayer`, from copies of the words in `cp`),
   runs the AES S-box circuit (`Impl/Aes/AArch64/Sbox.lean`, which spills
   to slots 0–47), and applies `P0` at the bytes `X0` and `X2` of each word
   and `P1` at `X1` and `X3` (`pLayer`, masking with `laneMask0` and
   `laneMask1`);
3. transposes back, and mixes each word's four S-box outputs as `G` does
   (`mixWord`: `Z = ⊕ᵣ rotr₃₂(s, 8r) & Mᵣ`, both halves at once), XORs the
   constant that `0xE7` and `0x2B` contribute to `G` (`gConst`) and stores
   the word back.

The masks are built in registers with `movz` and `movk` where they are
used, since the S-box overwrites every free register. Only bitwise
instructions, rotations and shifts by constants touch the data: no address
and no branch depends on it. `g16` writes the S-box's registers (`q 0 …
q 7`, `x14`–`x17`, `x19`–`x28`) and nothing else.
-/

namespace VG.Impl.Seed.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64 VG.Impl.Seed

/-! ## Scratch slots (of `x5`) -/

/-- `G`'s input and output words `2i` and `2i + 1`, after the S-box's spill
slots 0–47. -/
def tSlot (i : Nat) : Nat := 48 + i

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

/-- The masks of `ortho`, in AES's registers `m 4`, `m 5`, `m 6`. -/
def orthoMasks : List (Nat × BitVec 64) :=
  [(4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-! ## Registers -/

/-- Where the words are copied for the linear layers. -/
def cp : Nat → Reg
  | 0 => .x14 | 1 => .x15 | 2 => .x16 | 3 => .x17
  | 4 => .x19 | 5 => .x20 | 6 => .x23 | _ => .x24

def lane0 : Reg := .x25
def lane1 : Reg := .x26

/-- The mixing's masks: `M0`, and `Mᵣ` split into the bits that a rotation by
`8r` within a 32-bit half leaves in place (`mixLo r`) and those it wraps
(`mixHi r`); and the constant. -/
def mix0 : Reg := .x14
def mixLo : Nat → Reg
  | 1 => .x15 | 2 => .x16 | _ => .x17
def mixHi : Nat → Reg
  | 1 => .x19 | 2 => .x23 | _ => .x24
def cstR : Reg := .x25

/-- The mixing's masks and constant, as registers and values. -/
def mixMasks : List (Reg × BitVec 64) :=
  [(mix0, both (mixMask 0))] ++
  ((List.range 3).flatMap fun k =>
    [(mixLo (k + 1), both (mixMask (k + 1) &&& loBits (k + 1))),
     (mixHi (k + 1), both (mixMask (k + 1) &&& ~~~loBits (k + 1)))]) ++
  [(cstR, gConst)]

/-! ## The layers -/

/-- Copies the eight words to `cp`. -/
def copyQ : List Instr := (List.range 8).map fun j => movR (cp j) (q j)

/-- `q j := ⊕_{i ∈ rows j} x_i`, from the copies. -/
def xorRows (rows : List (List Nat)) : List Instr :=
  copyQ ++ (List.range 8).flatMap fun j =>
    match rows.getD j [] with
    | [] => [eorR (q j) (q j) (q j)]
    | i :: is => movR (q j) (cp i) :: is.map fun i => eorR (q j) (q j) (cp i)

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
    | none, false => [eorR (q j) (q j) (cp i)]
    | some m, true => [andR (q j) (cp i) m]
    | some m, false => [andR t0 (cp i) m, eorR (q j) (q j) t0]

/-- The input words of output word `j`. -/
def pIns (j : Nat) : List Nat :=
  (List.range 8).filter fun i => (p0Rows.getD j []).contains i || (p1Rows.getD j []).contains i

def pWord (j : Nat) : List Instr :=
  match pIns j with
  | [] => [eorR (q j) (q j) (q j)]
  | i :: is => pTerm j i true ++ is.flatMap fun i => pTerm j i false

def pLayer : List Instr := copyQ ++ imm lane0 laneMask0 ++ imm lane1 laneMask1 ++ (List.range 8).flatMap pWord

/-- `G`'s mixing of the S-box outputs in `x`, both 32-bit halves at once,
plus `gConst`, stored to `tSlot i` (`t0` and `t1` are clobbered). -/
def mixWord (x : Reg) (i : Nat) : List Instr :=
  [andR t1 x mix0] ++
  ((List.range 3).flatMap fun k =>
    [rorI t0 x (8 * (k + 1)), andR t0 t0 (mixLo (k + 1)), eorR t1 t1 t0,
     rorI t0 x (8 * (k + 1) + 32), andR t0 t0 (mixHi (k + 1)), eorR t1 t1 t0]) ++
  [eorR t1 t1 cstR, stS (tSlot i) t1]

/-- Loads the eight words, transposed, with `M` applied. -/
def g16In : List Instr :=
  (List.range 8).map (fun i => ldS (q i) (tSlot i)) ++ setMasks orthoMasks ++ ortho ++ mLayer

/-- From the S-box's output to the words of `G`. -/
def g16Out : List Instr :=
  pLayer ++ setMasks orthoMasks ++ ortho ++ mixMasks.flatMap (fun (r, v) => imm r v) ++
    (List.range 8).flatMap fun i => mixWord (q i) i

/-- `G` of the sixteen words in `tSlot 0 … tSlot 7`, in place. -/
def g16 : List Instr := g16In ++ sboxCode ++ g16Out

end VG.Impl.Seed.AArch64
