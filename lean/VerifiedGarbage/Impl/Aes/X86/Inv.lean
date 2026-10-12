module

public import VerifiedGarbage.Impl.Aes.X86.Linear

/-!
# The inverse round transformations of bitsliced AES on x86 (32-bit)

On the state of `Linear.lean` (two blocks in slots `0 … 7` of the scratch
buffer at `edi`), as BearSSL's `aes_ct` (Thomas Pornin, MIT licence)
computes them for decryption:

* InvSubBytes: the inverse S-box is the S-box between two applications of
  the inverse of its affine transformation (`invAff`), since
  `invSbox = inv ∘ aff⁻¹` and `sbox = aff ∘ inv`, so
  `aff⁻¹ ∘ sbox ∘ aff⁻¹ = inv ∘ aff⁻¹ = invSbox`.
* InvShiftRows: rows 1 and 3 rotate the other way within their 8 bits,
  then rows 2 and 3 by 4 (which is its own inverse).
* InvMixColumns: MixColumns after multiplying each column by
  `{04}x² + {05}` (`invMcPre`): `a'ᵣ = aᵣ ⊕ {04} • (aᵣ ⊕ aᵣ₊₂)`, since
  `{0b}x³ + {0d}x² + {09}x + {0e} = ({03}x³ + {01}x² + {01}x + {02}) ({04}x² + {05})`
  modulo `x⁴ + 1`.

Each uses the registers `tmpRegs` only, the state's slots and slots
`8 … 15`, which are the S-box's spill slots.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86

/-- The slot holding input word `k` during `invAff` and `invMcPre`. -/
def invSlot (k : Nat) : Nat := 8 + k

/-- The inverse of the S-box's affine transformation on every byte:
`bᵢ ← b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ`, `d = {05}`. -/
def invAff : List Instr :=
  ((List.range 8).flatMap fun k => [movS .eax k, st (invSlot k) .eax]) ++
  (List.range 8).flatMap fun i =>
    [movS .eax (invSlot ((i + 2) % 8)), xorS .eax (invSlot ((i + 5) % 8)),
      xorS .eax (invSlot ((i + 7) % 8))] ++
    (if i = 0 ∨ i = 2 then [notR .eax] else []) ++ [st i .eax]

/-- The inverse S-box on the state in slots `0 … 7`, in place. -/
def invSboxCode : List Instr := invAff ++ sboxCode ++ invAff

/-- InvShiftRows of slot `j`: rows 1 and 3 rotate by 2 bits the other way
within their 8 bits, then rows 2 and 3 by 4. -/
def invSrWord (j : Nat) : List Instr :=
  [movS .eax j,
   movR .ebx .eax, rorI .ebx 30, andI .ebx 0xFC00FC00, movR .ecx .eax, rorI .ecx 6,
   andI .ecx 0x03000300, andI .eax 0x00FF00FF, xorR .eax .ebx, xorR .eax .ecx,
   movR .ebx .eax, rorI .ebx 4, andI .ebx 0x0F0F0000, movR .ecx .eax, rorI .ecx 28,
   andI .ecx 0xF0F00000, andI .eax 0x0000FFFF, xorR .eax .ebx, xorR .eax .ecx,
   st j .eax]

def invShiftRows : List Instr := (List.range 8).flatMap invSrWord

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Each column times `{04}x² + {05}`: with `uⱼ = qⱼ ⊕ (qⱼ ⋙ 16)` (the
byte and the one two rows down) in slot `invSlot j`, `qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j =>
    [movS .eax j, movR .ebx .eax, rorI .ebx 16, xorR .eax .ebx, st (invSlot j) .eax]) ++
  ((List.range 8).flatMap fun j =>
    [movS .eax j] ++ (times4 j).map (fun k => xorS .eax (invSlot k)) ++ [st j .eax])

def invMixColumns : List Instr := invMcPre ++ mixColumns

end VG.Impl.Aes.X86
