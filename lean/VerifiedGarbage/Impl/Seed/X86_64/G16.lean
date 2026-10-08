import VerifiedGarbage.Impl.Aes.X86_64.Linear
import VerifiedGarbage.Impl.Seed.Layers

/-!
# SEED's G on sixteen words at once, bitsliced, on x86-64

The sixteen 32-bit words of `G`'s input are the eight 64-bit slots `tSlot i`
of the scratch buffer (`r9`), word `2i + h` in half `h` of slot `i`. `g16`
replaces each with `G` of it.

Both of SEED's S-boxes are affine functions of AES's: with the field
isomorphism `M` from SEED's field (`x⁸ + x⁶ + x⁵ + x + 1`) into AES's, and
linear maps `P0` and `P1`, `S0(x) = P0(S_AES(M x)) ⊕ 0xE7` and
`S1(x) = P1(S_AES(M x)) ⊕ 0x2B` (`Proof/Seed/Sbox.lean`). So the code

1. loads the eight words and transposes each byte position's 8×8 bit matrix
   (BearSSL's `ortho`, as AES's `Linear.lean`): word `j` (in `q j`) then holds
   bit `j` of the 64 bytes, byte `a` of slot `i` at bit `8a + i`;
2. applies `M` to every byte (`mLayer`), runs the AES S-box circuit
   (`Impl/Aes/X86_64/Sbox.lean`, which spills to slots 0–47), and applies
   `P0` at the bytes `X0` and `X2` of each word and `P1` at `X1` and `X3`
   (`pLayer`, masking with `laneMask0` and `laneMask1`);
3. transposes back, and mixes each word's four S-box outputs as `G` does
   (`mixWord`: `Z = ⊕ᵣ rotr₃₂(s, 8r) & Mᵣ`, both halves at once), XORs the
   constant that `0xE7` and `0x2B` contribute to `G` (`gConst`) and stores
   the word back.

Only bitwise instructions, rotations and shifts by constants touch the
data: no address and no branch depends on it. It uses the registers of the
AES S-box (`q 0 … q 7`, `t0`, `t1`) and the masks in `maskSlots`, which
`setG16Masks` writes.
-/

namespace VG.Impl.Seed.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64 VG.Impl.Seed

/-! ## Scratch slots (of `r9`) -/

/-- The spill slots of the S-box and the layers: slots 0–47 (`Sbox.lean`). -/
def spillSlot (k : Nat) : Nat := 1 + k

def orthoSlot1 : Nat := 48
def orthoSlot2 : Nat := 49
def orthoSlot4 : Nat := 50
/-- The bit positions of the bytes `X0` and `X2` of each word (`S0`). -/
def laneSlot0 : Nat := 51
/-- The bit positions of the bytes `X1` and `X3` of each word (`S1`). -/
def laneSlot1 : Nat := 52
/-- `M0` of the mixing, and `Mᵣ` split into the bits that a rotation by
`8r` within a 32-bit half leaves in place (`mixLoSlot r`) and those it
wraps (`mixHiSlot r`). -/
def mixSlot0 : Nat := 53
def mixLoSlot (r : Nat) : Nat := 52 + 2 * r
def mixHiSlot (r : Nat) : Nat := 53 + 2 * r
def constSlot : Nat := 60
/-- `G`'s input and output words `2i` and `2i + 1`. -/
def tSlot (i : Nat) : Nat := 61 + i

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

def maskSlots : List (Nat × BitVec 64) :=
  [(orthoSlot1, 0x5555555555555555), (orthoSlot2, 0x3333333333333333),
   (orthoSlot4, 0x0F0F0F0F0F0F0F0F), (laneSlot0, 0x00FF00FF00FF00FF),
   (laneSlot1, 0xFF00FF00FF00FF00), (mixSlot0, both (mixMask 0))] ++
  ((List.range 3).flatMap fun k =>
    [(mixLoSlot (k + 1), both (mixMask (k + 1) &&& loBits (k + 1))),
     (mixHiSlot (k + 1), both (mixMask (k + 1) &&& ~~~loBits (k + 1)))]) ++
  [(constSlot, gConst)]

/-- Writes the masks to their slots, through `t0`. -/
def setG16Masks : List Instr := setMasks maskSlots

/-! ## The layers -/

/-- BearSSL's `ortho`, with the masks in `orthoSlot1`, `orthoSlot2` and
`orthoSlot4`. -/
def orthoT : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 orthoSlot1 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 orthoSlot2 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 orthoSlot4 4)

/-- Saves the eight words to the first spill slots. -/
def spillQ : List Instr := (List.range 8).map fun j => st (spillSlot j) (q j)

/-- `q j := ⊕_{i ∈ rows j} x_i`, from the spilled `x`. -/
def xorRows (rows : List (List Nat)) : List Instr :=
  spillQ ++ (List.range 8).flatMap fun j =>
    match rows.getD j [] with
    | [] => [xorR (q j) (q j)]
    | i :: is => movS (q j) (spillSlot i) :: is.map fun i => xorS (q j) (spillSlot i)

def mLayer : List Instr := xorRows mRows

/-- One term of output word `j` of `pLayer`: input word `i`, at the S-box
lanes whose row of `P0` or `P1` has it. -/
def pTerm (j i : Nat) (first : Bool) : List Instr :=
  let in0 := (p0Rows.getD j []).contains i
  let in1 := (p1Rows.getD j []).contains i
  let mask : Option Nat := if in0 && in1 then none else if in0 then some laneSlot0 else some laneSlot1
  if !(in0 || in1) then []
  else match mask, first with
    | none, true => [movS (q j) (spillSlot i)]
    | none, false => [xorS (q j) (spillSlot i)]
    | some m, true => [movS (q j) (spillSlot i), andS (q j) m]
    | some m, false => [movS t0 (spillSlot i), andS t0 m, xorR (q j) t0]

/-- The input words of output word `j`. -/
def pIns (j : Nat) : List Nat :=
  (List.range 8).filter fun i => (p0Rows.getD j []).contains i || (p1Rows.getD j []).contains i

def pWord (j : Nat) : List Instr :=
  match pIns j with
  | [] => [xorR (q j) (q j)]
  | i :: is => pTerm j i true ++ is.flatMap fun i => pTerm j i false

def pLayer : List Instr := spillQ ++ (List.range 8).flatMap pWord

/-- `G`'s mixing of the S-box outputs in `x`, both 32-bit halves at once,
plus `gConst`, stored to `tSlot i` (`t0` and `t1` are clobbered). -/
def mixWord (x : Reg) (i : Nat) : List Instr :=
  [movR t1 x, andS t1 mixSlot0] ++
  ((List.range 3).flatMap fun k =>
    [movR t0 x, rorI t0 (8 * (k + 1)), andS t0 (mixLoSlot (k + 1)), xorR t1 t0,
     movR t0 x, rorI t0 (8 * (k + 1) + 32), andS t0 (mixHiSlot (k + 1)), xorR t1 t0]) ++
  [xorS t1 constSlot, st (tSlot i) t1]

/-- Loads the eight words, transposed, with `M` applied. -/
def g16In : List Instr := (List.range 8).map (fun i => movS (q i) (tSlot i)) ++ orthoT ++ mLayer

/-- From the S-box's output to the words of `G`. -/
def g16Out : List Instr :=
  pLayer ++ orthoT ++ (List.range 8).flatMap fun i => mixWord (q i) i

/-- `G` of the sixteen words in `tSlot 0 … tSlot 7`, in place. -/
def g16 : List Instr := g16In ++ sboxCode ++ g16Out

end VG.Impl.Seed.X86_64
