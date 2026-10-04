import VerifiedGarbage.Impl.Aes.Arm.Linear

/-!
# The inverse round transformations of bitsliced AES on ARMv7

On the state of `Linear.lean` (two blocks in `q 0 … q 7`, byte `r + 4c`
of block `b` at bit `8r + 2c + b`), as BearSSL's `aes_ct` (Thomas Pornin,
MIT licence) computes them for decryption:

* InvSubBytes: the inverse S-box is the S-box between two applications of
  the inverse of its affine transformation (`invAff`), since
  `invSbox = inv ∘ aff⁻¹` and `sbox = aff ∘ inv`, so
  `aff⁻¹ ∘ sbox ∘ aff⁻¹ = inv ∘ aff⁻¹ = invSbox`.
* InvShiftRows: row `r` rotates the other way, right by `8 − 2r` bits
  within its byte.
* InvMixColumns: MixColumns after multiplying each column by
  `{04}x² + {05}` (`invMcPre`): `a'ᵣ = aᵣ ⊕ {04} • (aᵣ ⊕ aᵣ₊₂)`, since
  `{0b}x³ + {0d}x² + {09}x + {0e} = ({03}x³ + {01}x² + {01}x + {02}) ({04}x² + {05})`
  modulo `x⁴ + 1`.

Each uses the state registers, the temporaries `t0`, `t1` and `u7` (and
`lr` in the S-box), and slots of the scratch buffer at `sb`: those of the
S-box, and 20–27 for the words `invAff` and `invMcPre` read.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The slot holding input word `k` during `invAff` and `invMcPre`. -/
def invSlot (k : Nat) : Nat := 20 + k

/-- The inverse of the S-box's affine transformation on every byte:
`bᵢ ← b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ`, `d = {05}`, with all
ones in `t1`. -/
def invAff : List Instr :=
  (List.range 8).map (fun k => stS (invSlot k) (q k)) ++
  [.mov t1 (.imm 0), .dp .sub t1 t1 (.imm 1)] ++
  (List.range 8).flatMap fun i =>
    [ldS (q i) (invSlot ((i + 2) % 8)), ldS t0 (invSlot ((i + 5) % 8)), eorR (q i) (q i) t0,
      ldS t0 (invSlot ((i + 7) % 8)), eorR (q i) (q i) t0] ++
    (if i = 0 ∨ i = 2 then [eorR (q i) (q i) t1] else [])

/-- The inverse S-box on the state in `q 0 … q 7`, in place. -/
def invSboxCode : List Instr := invAff ++ sboxCode ++ invAff

/-- InvShiftRows of one word: row `r` (bits `8r … 8r + 7`) rotates right
by `8 − 2r` bits within its byte. -/
def invSrWord (x : Reg) : List Instr :=
  [.dp .and t0 x (.imm 0x000000FF),
   .dp .and t1 x (.imm 0x0000C000), .dp .eor t0 t0 (rorOp t1 6),
   .dp .and t1 x (.imm 0x00003F00), .dp .eor t0 t0 (rorOp t1 30),
   .dp .and t1 x (.imm 0x00F00000), .dp .eor t0 t0 (rorOp t1 4),
   .dp .and t1 x (.imm 0x000F0000), .dp .eor t0 t0 (rorOp t1 28),
   .dp .and t1 x (.imm 0xFC000000), .dp .eor t0 t0 (rorOp t1 2),
   .dp .and t1 x (.imm 0x03000000), .dp .eor t0 t0 (rorOp t1 26),
   movR x t0]

def invShiftRows : List Instr := (List.range 8).flatMap fun j => invSrWord (q j)

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Each column times `{04}x² + {05}`: with `uⱼ = qⱼ ⊕ (qⱼ ⋙ 16)` (the
byte and the one two rows down) in slot `invSlot j`, `qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j => [.dp .eor t0 (q j) (rorOp (q j) 16), stS (invSlot j) t0]) ++
  ((List.range 8).flatMap fun j => (times4 j).flatMap fun k =>
    [ldS t0 (invSlot k), eorR (q j) (q j) t0])

def invMixColumns : List Instr := invMcPre ++ mixColumns

end VG.Impl.Aes.Arm
