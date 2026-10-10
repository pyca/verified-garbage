import VerifiedGarbage.Impl.Aes.Arm.Linear
import VerifiedGarbage.Impl.Seed.W32

/-!
# SEED's G on eight words at once, bitsliced, on ARMv7

As on AArch64 (`Impl/Seed/AArch64/G16.lean`), on 32-bit words: the eight
words of `G`'s input are the slots `tSlot 0 … tSlot 7` of the scratch
buffer (`r8`), and `g8` replaces each with `G` of it. Both of SEED's S-boxes
are affine functions of AES's (`Proof/Seed/Sbox.lean`), so the code

1. loads the eight words and transposes each byte position's 8×8 bit matrix
   (AES's `ortho`, `Impl/Aes/Arm/Linear.lean`): `q j` then holds bit `j` of
   the 32 bytes, byte `a` of word `i` at bit `8a + i`;
2. applies `M` to every byte (`mLayer`, from copies of the planes in the
   slots `cpSlot j`), runs the AES S-box circuit (`Impl/Aes/Arm/Sbox.lean`,
   which spills to slots 0–31), and applies `P0` at the bytes `X0` and `X2`
   of each word and `P1` at `X1` and `X3` (`pLayer`, masking with
   `laneMask0` in `lr`: the bits of `X1` and `X3` of `x` are
   `x ⊕ (x & laneMask0)`);
3. transposes back, and mixes each word's four S-box outputs as `G` does
   (`mixWord`: `Z = ⊕ᵣ rotr(s, 8r) & Mᵣ`), XORs the constant that `0xE7`
   and `0x2B` contribute to `G` (`gConst32`), and stores the word back. The
   masks and the constant are kept in the slots `mixSlot r`.

Only bitwise instructions and rotations and shifts by constants touch the
data: no address and no branch depends on it. `g8` writes the S-box's
registers (`q 0 … q 7`, `r10`–`r12`, `lr`) and nothing else; `r9` is kept.
-/

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Seed VG.Impl.Seed.W32

/-! ## Scratch slots (of `r8`), after the S-box's slots 0–31 -/

/-- The copies of the planes for the linear layers. -/
def cpSlot (j : Nat) : Nat := 32 + j

/-- `G`'s input and output word `i`. -/
def tSlot (i : Nat) : Nat := 40 + i

/-- The masks `M0 … M3` (`r < 4`) and the constant (`r = 4`). -/
def mixSlot (r : Nat) : Nat := 48 + r

/-! ## The layers -/

/-- Stores the eight planes to their copies. -/
def copyQ : List Instr := (List.range 8).map fun j => stS (cpSlot j) (q j)

/-- `q j := ⊕_{i ∈ rows j} x_i`, from the copies. -/
def xorRows (rows : List (List Nat)) : List Instr :=
  copyQ ++ (List.range 8).flatMap fun j =>
    match rows.getD j [] with
    | [] => [eorR (q j) (q j) (q j)]
    | i :: is => ldS (q j) (cpSlot i) :: is.flatMap fun i => [ldS t0 (cpSlot i), eorR (q j) (q j) t0]

def mLayer : List Instr := xorRows mRows

/-- One term of output plane `j` of `pLayer`: plane `i` at the bytes whose
row of `P0` or `P1` has it (`lr` holds `laneMask0`). -/
def pTerm (j i : Nat) (first : Bool) : List Instr :=
  let in0 := (p0Rows.getD j []).contains i
  let in1 := (p1Rows.getD j []).contains i
  if !(in0 || in1) then []
  else if in0 && in1 then
    if first then [ldS (q j) (cpSlot i)] else [ldS t0 (cpSlot i), eorR (q j) (q j) t0]
  else if in0 then
    if first then [ldS t0 (cpSlot i), andR (q j) t0 .lr]
    else [ldS t0 (cpSlot i), andR t0 t0 .lr, eorR (q j) (q j) t0]
  else
    if first then [ldS t0 (cpSlot i), andR t1 t0 .lr, eorR (q j) t0 t1]
    else [ldS t0 (cpSlot i), eorR (q j) (q j) t0, andR t0 t0 .lr, eorR (q j) (q j) t0]

/-- The input planes of output plane `j`. -/
def pIns (j : Nat) : List Nat :=
  (List.range 8).filter fun i => (p0Rows.getD j []).contains i || (p1Rows.getD j []).contains i

def pWord (j : Nat) : List Instr :=
  match pIns j with
  | [] => [eorR (q j) (q j) (q j)]
  | i :: is => pTerm j i true ++ is.flatMap fun i => pTerm j i false

def pLayer : List Instr := copyQ ++ imm32 .lr laneMask0 ++ (List.range 8).flatMap pWord

/-- The masks and the constant of the mixing, with their slots. -/
def mixConsts : List (Nat × BitVec 32) :=
  (List.range 4).map (fun r => (mixSlot r, mixMask r)) ++ [(mixSlot 4, gConst32)]

def storeMix : List Instr := mixConsts.flatMap fun (k, v) => imm32 t0 v ++ [stS k t0]

/-- `G`'s mixing of the S-box outputs in `x`, plus `gConst32`, stored to
`tSlot i` (`t0` and `t1` are clobbered). -/
def mixWord (x : Reg) (i : Nat) : List Instr :=
  [ldS t1 (mixSlot 0), andR t1 t1 x] ++
  ((List.range 3).flatMap fun k =>
    [ldS t0 (mixSlot (k + 1)), .dp .and t0 t0 (rorOp x (8 * (k + 1))), eorR t1 t1 t0]) ++
  [ldS t0 (mixSlot 4), eorR t1 t1 t0, stS (tSlot i) t1]

/-- Loads the eight words, transposed, with `M` applied. -/
def g8In : List Instr :=
  (List.range 8).map (fun i => ldS (q i) (tSlot i)) ++ ortho ++ mLayer

/-- From the S-box's output to the words of `G`. -/
def g8Out : List Instr :=
  pLayer ++ ortho ++ storeMix ++ (List.range 8).flatMap fun i => mixWord (q i) i

/-- `G` of the eight words in `tSlot 0 … tSlot 7`, in place. -/
def g8 : List Instr := g8In ++ sboxCode ++ g8Out

end VG.Impl.Seed.Arm
