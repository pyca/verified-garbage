module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Two Curve25519 field products in AdvSIMD, in radix 2²⁵·⁵

`prod2 o f₁ g₁ f₂ g₂` computes the products `[f₁] · [g₁]` (lane 0) and
`[f₂] · [g₂]` (lane 1) of field elements in the scalar format (four 64-bit
words at `[x0 + off]`, any value below 2²⁵⁶), as ten radix-2²⁵·⁵ limbs:
limb `k` of each product is a 64-bit lane of the vector stored at
`o + 16 k`, so that the product is `Σ limb_k · 2^⌈25.5 k⌉` modulo
`p = 2²⁵⁵ - 19`. The limbs are carried once (Bernstein's order, as
curve25519-donna does), so each is below `2²⁷`; the caller adds them up
exactly (`Hybrid.lean`).

Each operand pair is split into radix-2²⁵·⁵ limbs (`convert`): limb `i` of
both elements in the 32-bit lanes 0 and 1 of a vector. The products follow
the schoolbook formula of Bernstein's and Lenngren's implementations: limb
`i` of `f` times limb `j` of `g` goes to coefficient `i + j mod 10`, times 19
if `i + j ≥ 10` and times 2 if `i` and `j` are both odd. The 19 multiples of
`g` are precomputed (`mul .4s`), and the doubled odd limbs of `f` are the
upper halves of its vectors, which `umull2`/`umlal2` multiply by the upper
halves of `g`'s (copies of the lower ones).

The code reads no general-purpose register but `x0`, and writes none, so it
interleaves with scalar code. It uses every vector register; the caller saves
`v8`–`v15`. The constants it needs (the limb masks and `19` in each 32-bit
lane) are at `CONST`, written once by the caller.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Neon

open VG.AArch64

/-- The rows of the first operands, as `convert` leaves them. -/
def FBUF : Nat := 784
/-- The constants: `2²⁶ - 1` and `2²⁵ - 1` in each 64-bit lane, and `19` in each 32-bit lane. -/
def CONST : Nat := 1104
def M26 : Nat := CONST
def M25 : Nat := CONST + 16
def C19 : Nat := CONST + 32

def V (n : Nat) : VReg := VReg.ofNat n

def ldq (t : Nat) (off : Nat) : Instr := .ldrq (V t) .x0 off
def stq (t : Nat) (off : Nat) : Instr := .strq (V t) .x0 off
def vo (op : VOp) : Instr := .vop op

/-- The bit offset of limb `i`, `⌈25.5 i⌉`. -/
def limbOff (i : Nat) : Nat := [0, 26, 51, 77, 102, 128, 153, 179, 204, 230].getD i 0

/-- The width of limb `i` after a carry: 26 bits for even `i`, 25 for odd. -/
def width (i : Nat) : Nat := if i % 2 = 0 then 26 else 25

/-- The mask register of width `w`: `M26` in `m₂₆`, `M25` in `m₂₅`. -/
def maskOf (m₂₆ m₂₅ : Nat) (i : Nat) : Nat := if i % 2 = 0 then m₂₆ else m₂₅

/-- Limb `i` of the two elements whose words are in `v_{w₀}`–`v_{w₀+3}` (word `k`
of each element in 64-bit lane `0` or `1` of `v_{w₀+k}`), into the 64-bit
lanes of `v_d`: the bits `limbOff i` up to `limbOff (i + 1)` (to bit 256 for
limb 9), masked with `v_{m₂₆}` or `v_{m₂₅}`; a limb across two words takes
the second's bits from `v_t`. -/
def limb (w₀ m₂₆ m₂₅ d t i : Nat) : List Instr :=
  let o := limbOff i
  let k := o / 64
  let sh := o % 64
  let src := V (w₀ + k)
  let m := V (maskOf m₂₆ m₂₅ i)
  if sh = 0 then [vo (.logic .and (V d) src m)]
  else if i = 9 ∨ i = 4 then [vo (.shift .ushr .d2 (V d) src sh)]
  else if sh + width i ≤ 64 then
    [vo (.shift .ushr .d2 (V d) src sh), vo (.logic .and (V d) (V d) m)]
  else
    [vo (.shift .ushr .d2 (V d) src sh), vo (.shift .shl .d2 (V t) (V (w₀ + k + 1)) (64 - sh)),
      vo (.add .d2 (V d) (V d) (V t)), vo (.logic .and (V d) (V d) m)]

/-- The words of `[a₁]` (lane 0) and `[a₂]` (lane 1) into `v_{w₀}`–`v_{w₀+3}`,
by way of `v_{t}` and `v_{t+1}`. -/
def words (a₁ a₂ w₀ t : Nat) : List Instr :=
  (List.range 2).flatMap fun k =>
    [ldq t (a₁ + 16 * k), ldq (t + 1) (a₂ + 16 * k),
      vo (.perm .trn1 .d2 (V (w₀ + 2 * k)) (V t) (V (t + 1))),
      vo (.perm .trn2 .d2 (V (w₀ + 2 * k + 1)) (V t) (V (t + 1)))]

/-- The limbs of the second operands into `v0`–`v9` (limb `j` of both
elements in each half), and their 19 multiples into `v10`–`v18` (`j = 1 … 9`). -/
def convertG (g₁ g₂ : Nat) : List Instr :=
  [ldq 24 M26, ldq 25 M25, ldq 26 C19] ++ words g₁ g₂ 19 27 ++
  ((List.range 10).flatMap fun j =>
    limb 19 24 25 28 29 j ++ [vo (.perm .uzp1 .s4 (V j) (V 28) (V 28))]) ++
  (List.range 9).flatMap fun j => [vo (.mul (V (10 + j)) (V (j + 1)) (V 26))]

/-- The limbs of the first operands, row `i` at `FBUF + 16 i`: limb `i` of both
elements in the lower half, and in the upper half the same, doubled for odd `i`. -/
def convertF (f₁ f₂ : Nat) : List Instr :=
  [ldq 24 M26, ldq 25 M25] ++ words f₁ f₂ 19 27 ++
  ((List.range 10).flatMap fun i =>
    limb 19 24 25 28 29 i ++
    (if i % 2 = 1 then [vo (.shift .shl .d2 (V 29) (V 28) 1), vo (.perm .uzp1 .s4 (V 30) (V 28) (V 29))]
     else [vo (.perm .uzp1 .s4 (V 30) (V 28) (V 28))]) ++
    [stq 30 (FBUF + 16 * i)])

/-- The second operand's vector for row `i`, column `k`: `g_j` or `19 g_j`
(`j = k - i mod 10`). -/
def gReg (i k : Nat) : Nat :=
  let j := (k + 10 - i) % 10
  if i + j ≥ 10 then 9 + j else j

/-- Whether the product of row `i`, column `k` is doubled: both limbs odd. -/
def doubled (i k : Nat) : Bool := i % 2 == 1 && ((k + 10 - i) % 10) % 2 == 1

/-- Row `i`: limb `i` of `f` (from `FBUF`, into `v29`) times every limb of `g`,
into the coefficients `v19`–`v28`. -/
def row (i : Nat) : List Instr :=
  ldq 29 (FBUF + 16 * i) ::
  (List.range 10).flatMap fun k =>
    [if i = 0 then vo (.umull false (V (19 + k)) (V 29) (V (gReg i k)))
     else vo (.umlal (doubled i k) (V (19 + k)) (V 29) (V (gReg i k)))]

def products : List Instr := (List.range 10).flatMap row

/-- Carry coefficient `i` into `i + 1` (19 times into 0 for `i = 9`): masks in
`v0` (26 bits) and `v1` (25 bits), temporaries `v2`, `v3`. -/
def carry (i : Nat) : List Instr :=
  let h := V (19 + i)
  let n := V (19 + (i + 1) % 10)
  [vo (.shift .ushr .d2 (V 2) h (width i)), vo (.logic .and h h (V (maskOf 0 1 i)))] ++
  (if i = 9 then
    [vo (.shift .shl .d2 (V 3) (V 2) 4), vo (.add .d2 (V 3) (V 3) (V 2)), vo (.add .d2 (V 2) (V 2) (V 2)),
      vo (.add .d2 (V 2) (V 3) (V 2))]
   else []) ++
  [vo (.add .d2 n n (V 2))]

/-- The carry order: three rounds, each reading coefficients no earlier carry of
the round changed, so that their carries run at once rather than in a chain:
`8 … 0` (every coefficient into the next), then `9` (into `0`, 19 times) and
`8 … 1`, then `0`. Two of the carries depend on another (`9` on `8`, the last
`0` on `9`), against eight in the chain `4 → 9 → 0 → 1` of curve25519-donna's
order. -/
def carryOrder : List Nat := [8, 7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def carries : List Instr := [ldq 0 M26, ldq 1 M25] ++ carryOrder.flatMap carry

/-- The limbs of `[f₁] · [g₁]` and `[f₂] · [g₂]`, limb `k` at `o + 16 k`. -/
def prod2 (o f₁ g₁ f₂ g₂ : Nat) : List Instr :=
  convertF f₁ f₂ ++ convertG g₁ g₂ ++ products ++ carries ++
  (List.range 10).flatMap fun k => [stq (19 + k) (o + 16 * k)]

end VG.Impl.X25519.AArch64.Neon
