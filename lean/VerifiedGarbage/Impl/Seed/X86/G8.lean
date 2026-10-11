import VerifiedGarbage.Impl.Aes.X86.Linear
import VerifiedGarbage.Impl.Seed.W32

/-!
# SEED's G on eight words at once, bitsliced, on x86 (32-bit)

As on ARMv7 (`Impl/Seed/Arm/G8.lean`): the eight words of `G`'s input are
the slots `tSlot 0 … tSlot 7` of the scratch buffer (`edi`), and `g8`
replaces each with `G` of it. The planes live in slots `0 … 7`, where AES's
`ortho` and S-box circuit (`Impl/Aes/X86/Sbox.lean`, which spills to slots
8–63) work on them, so the code

1. copies the eight words to slots `0 … 7` and transposes each byte
   position's 8×8 bit matrix (`ortho`): slot `j` then holds bit `j` of the
   32 bytes, byte `a` of word `i` at bit `8a + i`;
2. applies `M` to every byte (`mLayer`, from copies of the planes in the
   slots `cpSlot j`), runs the S-box circuit, and applies `P0` at the bytes
   `X0` and `X2` of each word and `P1` at `X1` and `X3` (`pLayer`, masking
   with `laneMask0` and its complement);
3. transposes back, and mixes each word's four S-box outputs as `G` does
   (`mixWord`: `Z = ⊕ᵣ rotr(s, 8r) & Mᵣ`), XORs the constant that `0xE7`
   and `0x2B` contribute to `G` (`gConst32`), and stores the word back.

Only bitwise instructions and rotations and shifts by constants touch the
data: no address and no branch depends on it. `g8` writes the S-box's
registers `tmpRegs` (`eax`, `ebx`, `ecx`, `edx`, `ebp`) and nothing else;
`esi` is kept.
-/

namespace VG.Impl.Seed.X86

open VG.X86 VG.Impl.Aes.X86 VG.Impl.Seed VG.Impl.Seed.W32

/-! ## Scratch slots (of `edi`), after the S-box's slots 0–63 -/

/-- The copies of the planes for the linear layers. -/
def cpSlot (j : Nat) : Nat := 64 + j

/-- `G`'s input and output word `i`. -/
def tSlot (i : Nat) : Nat := 72 + i

def xorI (d : Reg) (v : BitVec 32) : Instr := .alu .xor d (.imm v)

/-! ## The layers -/

/-- Copies the eight planes. -/
def copyQ : List Instr := (List.range 8).flatMap fun j => [movS .eax j, st (cpSlot j) .eax]

/-- Plane `j := ⊕_{i ∈ rows j} x_i`, from the copies. -/
def xorRows (rows : List (List Nat)) : List Instr :=
  copyQ ++ (List.range 8).flatMap fun j =>
    match rows.getD j [] with
    | [] => [xorR .eax .eax, st j .eax]
    | i :: is => movS .eax (cpSlot i) :: is.map (fun i => xorS .eax (cpSlot i)) ++ [st j .eax]

def mLayer : List Instr := xorRows mRows

/-- One term of output plane `j` of `pLayer`: plane `i` at the bytes whose
row of `P0` or `P1` has it, into `eax` (through `ebx`). -/
def pTerm (j i : Nat) (first : Bool) : List Instr :=
  let in0 := (p0Rows.getD j []).contains i
  let in1 := (p1Rows.getD j []).contains i
  if !(in0 || in1) then []
  else if in0 && in1 then
    if first then [movS .eax (cpSlot i)] else [xorS .eax (cpSlot i)]
  else
    let mask := if in0 then laneMask0 else ~~~laneMask0
    if first then [movS .eax (cpSlot i), andI .eax mask]
    else [movS .ebx (cpSlot i), andI .ebx mask, xorR .eax .ebx]

/-- The input planes of output plane `j`. -/
def pIns (j : Nat) : List Nat :=
  (List.range 8).filter fun i => (p0Rows.getD j []).contains i || (p1Rows.getD j []).contains i

def pWord (j : Nat) : List Instr :=
  (match pIns j with
   | [] => [xorR .eax .eax]
   | i :: is => pTerm j i true ++ is.flatMap fun i => pTerm j i false) ++ [st j .eax]

def pLayer : List Instr := copyQ ++ (List.range 8).flatMap pWord

/-- `G`'s mixing of the S-box outputs of word `i` (in slot `i`), plus
`gConst32`, stored to `tSlot i` (through `eax`, `ebx`, `ecx`). -/
def mixWord (i : Nat) : List Instr :=
  [movS .eax i, movR .ebx .eax, andI .ebx (mixMask 0)] ++
  ((List.range 3).flatMap fun k =>
    [movR .ecx .eax, rorI .ecx (8 * (k + 1)), andI .ecx (mixMask (k + 1)), xorR .ebx .ecx]) ++
  [xorI .ebx gConst32, st (tSlot i) .ebx]

/-- Copies the eight words to the planes, transposed, with `M` applied. -/
def g8In : List Instr :=
  (List.range 8).flatMap (fun i => [movS .eax (tSlot i), st i .eax]) ++ ortho ++ mLayer

/-- From the S-box's output to the words of `G`. -/
def g8Out : List Instr := pLayer ++ ortho ++ (List.range 8).flatMap mixWord

/-- `G` of the eight words in `tSlot 0 … tSlot 7`, in place. -/
def g8 : List Instr := g8In ++ sboxCode ++ g8Out

end VG.Impl.Seed.X86
