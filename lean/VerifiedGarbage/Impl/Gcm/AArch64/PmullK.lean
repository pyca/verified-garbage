module

public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull

/-!
# GHASH with PMULL and EOR3 on AArch64: Karatsuba multiplication

`vg_ghash_aes_sha3`, `vg_ghash_with_powers_aes_sha3` and
`vg_ghash_store_powers_aes_sha3`: `vg_ghash_aes`'s functions
(`Impl.Gcm.AArch64.Pmull`) for CPUs with FEAT_SHA3 too, whose eight-, four-
and two-block steps multiply with three `pmull`s per block instead of four, and
add the products with `eor3`.

On Neoverse N2 `pmull` and `eor3` issue to one vector pipe (V0) and the other
vector instructions to either: the four `pmull`s of a block in `vg_ghash_aes`
already fill V0 for most of its loop, so `eor3` alone would add to V0 what it
saves on the other pipe. Karatsuba's product needs one `pmull` fewer per block.

* Of a block `a` as loaded and a key `t` (`s` its halves swapped, as `sReg`
  holds it), `vg_ghash_aes` adds `pmull a, s` to `hi`, `pmull2 a, s` to `lo`,
  and `pmull a, t` and `pmull2 a, t` to `mid`. Here `mid` collects
  `(a₀ + a₁) · (t₀ + t₁)` instead (`kprod`): `a₀ + a₁` is in both halves of
  `ext a, a, #8` plus `a`, and `t₀ + t₁` is the key's `kReg` lane, computed once
  per call (`keys`). The sum of the products is then `mid + hi + lo`
  (`reduceK`, which adds them with the reduction's first step).
* The blocks go two at a time (`kpair`), whose products are added with three
  `eor3`s (the first pair's with `eor`s, to the products alone), the first
  block of a step, which `Y` is added to, in the last pair.
* The keys `t₀ + t₁` of `H'` to `H'⁸` are in `kReg`, two to a register, in
  place of `H'⁵` to `H'⁸` (`tReg`), which the loops do not use: `H'ᵏ` with
  its halves swapped (`sReg`) gives the other products. The loops use `tReg 1`
  to `tReg 3` as temporaries.
* `vg_ghash_store_powers_aes_sha3` stores `H'ᵏ` from `sReg` after the loops.
* A single block (`body1K`) has its products computed into `hi`, `lo` and
  `mid` directly.

Only caller-saved registers are used (`x5`–`x8`, `v0`–`v7`, `v16`–`v31`),
and `scratch` is not. Every branch and every address depends only on the
pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64.PmullK

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (Y C LO MID HI A T tReg sReg loadRev advance epilogue prologue powers
  prologueW prologueS pwOff)

/-! Registers: as `vg_ghash_aes`'s, with `v2` a temporary, `v16`–`v18` the
second block of a pair and its products, and `v20`–`v23` the keys. -/

abbrev P : VReg := .v2
abbrev A₂ : VReg := .v16
abbrev B₂ : VReg := .v17
abbrev P₂ : VReg := .v18

/-- The register of the keys of `H'²ʲ⁺¹` (low lane) and `H'²ʲ⁺²` (high lane). -/
def kReg : Nat → VReg
  | 0 => .v20 | 1 => .v21 | 2 => .v22 | _ => .v23

/-- Whether the key of `H'ᵏ` is in the high lane of its register. -/
def kHi (k : Nat) : Bool := (k - 1) % 2 == 1

/-- The register of the key of `H'ᵏ`. -/
def keyOf (k : Nat) : VReg := kReg ((k - 1) / 2)

/-- The keys of `H'²ʲ⁺¹` and `H'²ʲ⁺²`: `s ⊕ t` has `t₀ ⊕ t₁` in both lanes. -/
def keyPair (j : Nat) : List Instr :=
  [.vop (.logic .eor P (sReg (2 * j + 1)) (tReg (2 * j + 1))),
   .vop (.logic .eor A (sReg (2 * j + 2)) (tReg (2 * j + 2))), .vop (.ext (kReg j) P A 8)]

/-- The keys of `H'` to `H'⁸`, the last first, since `kReg 3` is `tReg 8`. -/
def keys : List Instr := keyPair 3 ++ keyPair 2 ++ keyPair 1 ++ keyPair 0

/-- The key of `H'` alone. -/
def key1 : List Instr := [.vop (.logic .eor (kReg 0) (sReg 1) (tReg 1))]

/-- The products of the block `a`, as loaded, and `H'ᵏ`: `p ← a₀ · s₀`
(`hi`), `a ← a₁ · s₁` (`lo`), `b ← (a₀ + a₁) · (t₀ + t₁)`. -/
def kprod (a b p : VReg) (k : Nat) : List Instr :=
  [.vop (.ext b a a 8), .vop (.logic .eor b b a), .vop (.pmull false p a (sReg k)),
   .vop (.pmull true a a (sReg k)), .vop (.pmull (kHi k) b b (keyOf k))]

/-- Blocks `j₁` and `j₂` and their products by `H'ᵏ¹` and `H'ᵏ²`, `Y` added to
the second if `y`. -/
def kpair (j₁ k₁ j₂ k₂ : Nat) (y : Bool) : List Instr :=
  loadRev A .x2 (16 * j₁) ++ kprod A T P k₁ ++ loadRev A₂ .x2 (16 * j₂) ++
    (if y then [.vop (.logic .eor A₂ A₂ Y)] else []) ++ kprod A₂ B₂ P₂ k₂

/-- A pair's products, the first: the sums. -/
def addFirst : List Instr :=
  [.vop (.logic .eor HI P P₂), .vop (.logic .eor LO A A₂), .vop (.logic .eor MID T B₂)]

/-- A pair's products added. -/
def addNext : List Instr :=
  [.vop (.eor3 HI HI P P₂), .vop (.eor3 LO LO A A₂), .vop (.eor3 MID MID T B₂)]

/-- `vg_ghash_aes`'s `reduce` of the product `hi : mid ⊕ hi ⊕ lo : lo`,
into `Y`, with `eor3`: `u = mid ⊕ (swap(lo) ⊕ lo ⊕ hi) ⊕ pmull(lo₀, c)`,
then `swap(hi) ⊕ u ⊕ swap(pmull(u₀, c))`. -/
def reduceK : List Instr :=
  [.vop (.pmull false T LO C), .vop (.ext P LO LO 8), .vop (.eor3 P P LO HI),
   .vop (.eor3 MID MID P T), .vop (.pmull false T MID C), .vop (.ext HI HI HI 8),
   .vop (.ext T T T 8), .vop (.eor3 Y HI MID T)]

/-- Pair `m` of a step of `k` blocks: blocks `2m + 1` and `2m + 2`, by
`H'ᵏ⁻²ᵐ⁻¹` and `H'ᵏ⁻²ᵐ⁻²`, or, the last, block `k - 1` by `H'` and the first
block, plus `Y`, by `H'ᵏ`. -/
def pairAt (k m : Nat) : List Instr :=
  if m + 1 = k / 2 then kpair (k - 1) 1 0 k true
  else kpair (2 * m + 1) (k - 2 * m - 1) (2 * m + 2) (k - 2 * m - 2) false

/-- `k` blocks (`k` = 2, 4 or 8), then the pointer and the counts. -/
def bodyK (k : Nat) : List Instr :=
  pairAt k 0 ++ addFirst ++ (List.range (k / 2 - 1)).flatMap (fun m => pairAt k (m + 1) ++ addNext) ++
    reduceK ++ advance k

/-- The products of the block in `A` and `H'`, into `hi`, `lo` and `mid`. -/
def single : List Instr :=
  [.vop (.ext MID A A 8), .vop (.logic .eor MID MID A), .vop (.pmull false HI A (sReg 1)),
   .vop (.pmull true LO A (sReg 1)), .vop (.pmull (kHi 1) MID MID (keyOf 1))]

/-- One block, plus `Y`, by `H'`. -/
def body1K : List Instr :=
  loadRev A .x2 0 ++ ([.vop (.logic .eor A A Y)] : List Instr) ++ single ++ reduceK ++ advance 1

/-- The last `n mod 8` blocks, once the powers and keys are set up. -/
def tailK : Prog isa :=
  .seq (.block [.lsr .x .x6 .x3 2]) (.seq (.ite (.zero .x .x6) (.block []) (.block (bodyK 4)))
    (.seq (.block [.lsr .x .x6 .x3 1]) (.seq (.ite (.zero .x .x6) (.block []) (.block (bodyK 2)))
      (.ite (.zero .x .x3) (.block []) (.block body1K)))))

/-- GHASH from `vg_ghash_aes`'s prologue, which sets up `H'`: with fewer than
eight blocks, `H'`'s key and one block at a time; otherwise `H'²` to `H'⁸`
and their keys first. -/
def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite (.zero .x .x5)
        (.ite (.zero .x .x3) (.block []) (.seq (.block key1) (.loop (.block body1K) (.nonzero .x .x3))))
        (.seq (.block (powers ++ keys)) (.seq (.loop (.block (bodyK 8)) (.nonzero .x .x5)) tailK)))
      (.block epilogue))

/-- GHASH from the prologue `pro`, which sets up `H'` to `H'⁸` and their keys,
then `fin` after the epilogue. -/
def ghashAllK (pro fin : List Instr) : Prog isa :=
  .seq (.block pro)
    (.seq (.ite (.zero .x .x5)
        (.ite (.zero .x .x3) (.block []) (.loop (.block body1K) (.nonzero .x .x3)))
        (.seq (.loop (.block (bodyK 8)) (.nonzero .x .x5)) tailK))
      (.block (epilogue ++ fin)))

def ghashW : Prog isa := ghashAllK (prologueW ++ keys) []

/-- `H'ᵏ` stored to `pw` (`x8`), from `sReg k`. -/
def storePwK (k : Nat) : List Instr := [.vop (.ext P (sReg k) (sReg k) 8), .strq P .x8 (pwOff k)]

/-- `H'` to `H'⁸` stored. -/
def storesSK : List Instr :=
  storePwK 1 ++ storePwK 2 ++ storePwK 3 ++ storePwK 4 ++ storePwK 5 ++ storePwK 6 ++ storePwK 7 ++
    storePwK 8

def ghashS : Prog isa := ghashAllK (prologueS ++ keys) storesSK

end VG.Impl.Gcm.AArch64.PmullK
