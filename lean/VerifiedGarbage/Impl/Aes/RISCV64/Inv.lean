module

public import VerifiedGarbage.Impl.Aes.RISCV64.Linear

/-!
# The inverse round transformations of bitsliced AES on RISC-V

On the state of `Linear.lean` (four blocks in `q 0 … q 7`), as on PPC64LE
(`Impl/Aes/PPC64LE/Inv.lean`), and as BearSSL's `aes_ct64` (Thomas Pornin,
MIT licence) computes them for decryption:

* InvSubBytes: the inverse S-box is the S-box between two applications of
  the inverse of its affine transformation (`invAff`), since
  `invSbox = inv ∘ aff⁻¹` and `sbox = aff ∘ inv`, so
  `aff⁻¹ ∘ sbox ∘ aff⁻¹ = inv ∘ aff⁻¹ = invSbox`.
* InvShiftRows: rows 1 and 3 rotate the other way within their 16 bits,
  then rows 2 and 3 by 8 (which is its own inverse).
* InvMixColumns: MixColumns after multiplying each column by
  `{04}x² + {05}` (`invMcPre`): `a'ᵣ = aᵣ ⊕ {04} • (aᵣ ⊕ aᵣ₊₂)`, since
  `{0b}x³ + {0d}x² + {09}x + {0e} = ({03}x³ + {01}x² + {01}x + {02}) ({04}x² + {05})`
  modulo `x⁴ + 1`.

Each writes only the state registers and the S-box's temporaries.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-- The register holding input word `k` during `invAff` and `invMcPre`. -/
def iv : Nat → Reg
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | 3 => .t3
  | 4 => .t4 | 5 => .t5 | 6 => .t6 | _ => .a6

/-- The temporary of `invMcPre`'s rotations. -/
def ivt : Reg := .a7

/-- The inverse of the S-box's affine transformation on every byte:
`bᵢ ← b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ`, `d = {05}`. -/
def invAff : List Instr :=
  (List.range 8).map (fun k => movR (iv k) (q k)) ++
  (List.range 8).flatMap fun i =>
    [xorR (q i) (iv ((i + 2) % 8)) (iv ((i + 5) % 8)), xorR (q i) (q i) (iv ((i + 7) % 8))] ++
    (if i = 0 ∨ i = 2 then [notR (q i)] else [])

/-- The inverse S-box on the state in `q 0 … q 7`, in place. -/
def invSboxCode : List Instr := invAff ++ sboxCode ++ invAff

/-- The masks of InvShiftRows, and their first slot. -/
def invSrMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0xFFF00000FFF00000), (3, 0x000F0000000F0000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]
def invSrSlot : Nat := 70

/-- InvShiftRows of one word: rows 1 and 3 rotate by 4 bits the other way
within their 16 bits, then rows 2 and 3 by 8. -/
def invSrWord (x : Reg) : List Instr :=
  [shlI t0 x 4, andR t0 t0 (m 2), shrI t1 x 12, andR t1 t1 (m 3),
   andR x x (m 1), xorR x x t0, xorR x x t1,
   shrI t0 x 8, andR t0 t0 (m 5), shlI t1 x 8, andR t1 t1 (m 6),
   andR x x (m 4), xorR x x t0, xorR x x t1]

def invShiftRows : List Instr :=
  loadMasks invSrSlot invSrMasks ++ (List.range 8).flatMap fun j => invSrWord (q j)

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Each column times `{04}x² + {05}`: with `uⱼ = qⱼ ⊕ (qⱼ ⋙ 32)` (the
byte and the one two rows down) in `iv j`, `qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j =>
    [shrI ivt (q j) 32, shlI (iv j) (q j) 32, xorR (iv j) (iv j) ivt, xorR (iv j) (iv j) (q j)]) ++
  ((List.range 8).flatMap fun j => (times4 j).map fun k => xorR (q j) (q j) (iv k))

def invMixColumns : List Instr := invMcPre ++ mixColumns

end VG.Impl.Aes.RISCV64
