import VerifiedGarbage.Impl.Aes.X86_64.Linear

/-!
# The inverse round transformations of bitsliced AES on x86-64

On the state of `Linear.lean` (four blocks in `q 0 … q 7`), as BearSSL's
`aes_ct64` (Thomas Pornin, MIT licence) computes them for decryption:

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

Each uses the state registers, the temporaries `t0` and `t1`, and slots of
the scratch buffer at `r9`: the all-ones slot, 20–27 and those of the
layers it reuses.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- The slot holding input word `k` during `invAff` and `invMcPre`. -/
def invSlot (k : Nat) : Nat := 20 + k

/-- The inverse of the S-box's affine transformation on every byte:
`bᵢ ← b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ`, `d = {05}`. -/
def invAff : List Instr :=
  [ones t0, st onesSlot t0] ++ (List.range 8).map (fun k => st (invSlot k) (q k)) ++
  (List.range 8).flatMap fun i =>
    [movS (q i) (invSlot ((i + 2) % 8)), xorS (q i) (invSlot ((i + 5) % 8)),
      xorS (q i) (invSlot ((i + 7) % 8))] ++
    (if i = 0 ∨ i = 2 then [xorS (q i) onesSlot] else [])

/-- The inverse S-box on the state in `q 0 … q 7`, in place. -/
def invSboxCode : List Instr := invAff ++ sboxCode ++ invAff

/-- The masks of InvShiftRows, in slots 1–6. -/
def invSrMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0xFFF00000FFF00000), (3, 0x000F0000000F0000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]

/-- InvShiftRows of one word: rows 1 and 3 rotate by 4 bits the other way
within their 16 bits, then rows 2 and 3 by 8. -/
def invSrWord (x : Reg) : List Instr :=
  [movR t0 x, rorI t0 60, andS t0 2, movR t1 x, rorI t1 12, andS t1 3,
   andS x 1, xorR x t0, xorR x t1,
   movR t0 x, rorI t0 8, andS t0 5, movR t1 x, rorI t1 56, andS t1 6,
   andS x 4, xorR x t0, xorR x t1]

def invShiftRows : List Instr :=
  setMasks invSrMasks ++ (List.range 8).flatMap fun j => invSrWord (q j)

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Each column times `{04}x² + {05}`: with `uⱼ = qⱼ ⊕ (qⱼ ⋙ 32)` (the
byte and the one two rows down) in slot `invSlot j`, `qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j =>
    [movR t0 (q j), rorI t0 32, xorR t0 (q j), st (invSlot j) t0]) ++
  ((List.range 8).flatMap fun j => (times4 j).map fun k => xorS (q j) (invSlot k))

def invMixColumns : List Instr := invMcPre ++ mixColumns

end VG.Impl.Aes.X86_64
