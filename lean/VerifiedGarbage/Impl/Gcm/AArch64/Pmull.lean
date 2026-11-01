module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Gcm.Clmul -- shake: keep (exports the existing PMULL constants)

/-!
# GHASH with PMULL on AArch64

`vg_ghash_aes(h = x0, y = x1, data = x2, n = x3, scratch = x4)`, with the
contract of `vg_ghash` (`Proof.Gcm.ghashContract`), for CPUs with FEAT_PMULL
(Rust's `aes` feature, hence the suffix: see `Artifacts/Gcm/AArch64.lean`).

The arithmetic is that of `Impl.Gcm.X86_64.Pclmul`. A block is loaded with
`ldr q` and `rev64 .16b`, which leaves the first eight bytes of the block,
as a big-endian value, in the low doubleword and the last eight in the high
one: the halves of the block's value (the first byte the most significant)
swapped. In the bit-reflected representation of SP 800-38D:

* the carry-less product of a loaded block `a` and a block `t` (in the
  block's order), with `s` the halves of `t` swapped, is `x · a · t`, as 256
  bits `hi : mid : lo` (`hi` holding the low powers): `pmull a, s` and
  `pmull2 a, s` give `hi` and `lo`, and `pmull a, t` and `pmull2 a, t` the
  two halves of `mid`;
* the product is reduced into 128 bits as `hi ⊕ fold(mid ⊕ fold(lo))`, where
  `fold(r)`, the halves of `r` swapped (`ext #8`) plus the `pmull` of its low
  half by the constant `0xc2 · 2⁵⁶` (`x + x² + x⁷`, reflected), is of the
  class of `x⁶⁴ · r`, so that `mul(a, t) = x · a · t` in GF(2¹²⁸); it is
  computed with its halves swapped, as a block is loaded;
* to cancel the factor `x`, the hash subkey is used as `H' = H · x⁻¹ =
  mul(H, x⁻²)`, `x⁻²` a constant;
* `H'ᵏ = mul(H'ⁱ, H'ʲ) = Hᵏ · x⁻¹` (`i + j = k`) for `k = 2 … 8` are
  computed once per call when there are at least eight blocks, and kept in
  registers, as they are and with their halves swapped; eight blocks at a time
  `Y ← mul(Y ⊕ X₁, H'⁸) ⊕ mul(X₂, H'⁷) ⊕ … ⊕ mul(X₈, H')`, reducing the sum of
  the eight products once, and adding the product of `Y ⊕ X₁` last so that
  only it and the reduction wait for the previous `Y`; the remaining blocks go
  four, two and one at a time (with one reduction each), or, if there are
  fewer than eight blocks in all, one at a time.
* `Y` is kept as loaded (its halves swapped), and stored with `rev64`.

Only caller-saved registers are used (`x5`–`x7`, `v0`–`v7`, `v16`–`v31`),
and `scratch` is not. Every branch and every address depends only on the
pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64.Pmull

open VG.AArch64

/-! Registers: `v0` `Y`, `v1` the reduction constant in both halves,
`v3`–`v5` the product (`lo`, `mid`, `hi`), `v6` a block, `v7` a
temporary, `v16`–`v23` `H'`–`H'⁸`, `v24`–`v31` the same with their halves
swapped. -/

abbrev Y : VReg := .v0
abbrev C : VReg := .v1
abbrev LO : VReg := .v3
abbrev MID : VReg := .v4
abbrev HI : VReg := .v5
abbrev A : VReg := .v6
abbrev T : VReg := .v7

/-- The register of `H'ᵏ`, `1 ≤ k ≤ 8`. -/
def tReg : Nat → VReg
  | 2 => .v17 | 3 => .v18 | 4 => .v19 | 5 => .v20 | 6 => .v21 | 7 => .v22 | 8 => .v23
  | _ => .v16

/-- The register of `H'ᵏ` with its halves swapped, `1 ≤ k ≤ 8`. -/
def sReg : Nat → VReg
  | 2 => .v25 | 3 => .v26 | 4 => .v27 | 5 => .v28 | 6 => .v29 | 7 => .v30 | 8 => .v31
  | _ => .v24

/- The reduction constant `0xc2 · 2⁵⁶`. -/
export VG.Impl.Gcm.Clmul (poly)

/- `x⁻²` (reflected): the high doubleword; the low one is 3. -/
export VG.Impl.Gcm.Clmul (xInv2Hi)

/-- Clear the product. -/
def zero : List Instr := [.vop (.movi0 LO), .vop (.movi0 MID), .vop (.movi0 HI)]

/-- Add the product of the loaded block `a` and the key `t` (`s` its halves swapped). -/
def acc (a s t : VReg) : List Instr :=
  [.vop (.pmull false T a s), .vop (.logic .eor HI HI T),
   .vop (.pmull true T a s), .vop (.logic .eor LO LO T),
   .vop (.pmull false T a t), .vop (.logic .eor MID MID T),
   .vop (.pmull true T a t), .vop (.logic .eor MID MID T)]

/-- The product, reduced, into `d` with its halves swapped:
`swap(hi ⊕ fold(u)) = swap(hi) ⊕ u ⊕ swap(pmull(u₀, c))` for
`u = mid ⊕ fold(lo)`, where `fold(r) = swap(r) ⊕ pmull(r₀, c)`, with `c =
0xc2 · 2⁵⁶`, is of the class of `x⁶⁴ · r`. -/
def reduce (d : VReg) : List Instr :=
  [.vop (.pmull false T LO C), .vop (.ext LO LO LO 8), .vop (.logic .eor MID MID LO),
   .vop (.logic .eor MID MID T), .vop (.pmull false T MID C), .vop (.ext HI HI HI 8),
   .vop (.logic .eor HI HI MID), .vop (.ext T T T 8), .vop (.logic .eor d HI T)]

/-- `d ← mul(a, t)` with its halves swapped, `a` as loaded, `s` the halves of `t` swapped. -/
def mul (d a s t : VReg) : List Instr := zero ++ acc a s t ++ reduce d

/-- The block at `[n, #off]` into `d`, as loaded. -/
def loadRev (d : VReg) (n : Reg) (off : Nat) : List Instr := [.ldrq d n off, .vop (.rev .rev64b d d)]

/-- Block `j` of the data into `v6`, as loaded. -/
def load (j : Nat) : List Instr := loadRev A .x2 (16 * j)

/-- `H'ᵏ = mul(H'ⁱ, H'ʲ)`, and its halves swapped. -/
def pow (k i j : Nat) : List Instr :=
  mul (sReg k) (sReg i) (sReg j) (tReg j) ++ ([.vop (.ext (tReg k) (sReg k) (sReg k) 8)] : List Instr)

/-- The reduction constant in both halves of `v1`, and `x⁻²` in
`v17` and, its halves swapped, in `v25`. -/
def consts : List Instr :=
  [.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5),
   .movz .x .x6 3 0, .movz .x .x7 0x4600 3,
   .vop (.ins .d2 (tReg 2) 0 .x6), .vop (.ins .d2 (tReg 2) 1 .x7),
   .vop (.ins .d2 (sReg 2) 0 .x7), .vop (.ins .d2 (sReg 2) 1 .x6)]

/-- `H` (as loaded), the constants, `H' = mul(H, x⁻²)` and `Y`. -/
def prologue : List Instr :=
  loadRev A .x0 0 ++ consts ++ mul (sReg 1) A (sReg 2) (tReg 2) ++
  ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr) ++ loadRev Y .x1 0 ++ ([.lsr .x .x5 .x3 3] : List Instr)

/-- `H'²` to `H'⁸`. -/
def powers : List Instr :=
  pow 2 1 1 ++ pow 3 2 1 ++ pow 4 2 2 ++ pow 5 4 1 ++ pow 6 4 2 ++ pow 7 4 3 ++ pow 8 4 4

/-- Block `j + 1` of `k`, by `H'ᵏ⁻ʲ⁻¹`. -/
def blk (k j : Nat) : List Instr := load (j + 1) ++ acc A (sReg (k - 1 - j)) (tReg (k - 1 - j))

/-- Past `k` blocks: the pointer, the count, and the count of groups of eight. -/
def advance (k : Nat) : List Instr :=
  [.addImm .x .x2 .x2 (16 * k), .subImm .x .x3 .x3 k, .lsr .x .x5 .x3 3]

/-- `k` blocks (`k` = 1 or 8), then the pointer and the counts. The first
block, which `Y` is added to, goes last, so that only its products and the
reduction wait for the previous `Y`. -/
def body (k : Nat) : List Instr :=
  zero ++ (List.range (k - 1)).flatMap (blk k) ++ load 0 ++ ([.vop (.logic .eor A A Y)] : List Instr) ++
  acc A (sReg k) (tReg k) ++ reduce Y ++ advance k

def epilogue : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x1 0]

/-- The last `n mod 8` blocks, once the powers are computed: four, two and one
at a time, as the bits of `n` say. -/
def tail : Prog isa :=
  .seq (.block [.lsr .x .x6 .x3 2]) (.seq (.ite (.zero .x .x6) (.block []) (.block (body 4)))
    (.seq (.block [.lsr .x .x6 .x3 1]) (.seq (.ite (.zero .x .x6) (.block []) (.block (body 2)))
      (.ite (.zero .x .x3) (.block []) (.block (body 1))))))

/-- GHASH from the prologue `pro`, which sets up `H'`, and the powers `pow`,
which set up `H'²` to `H'⁸` when there are at least eight blocks. -/
def ghashWith (pro pow : List Instr) : Prog isa :=
  .seq (.block pro)
    (.seq (.ite (.zero .x .x5)
        (.ite (.zero .x .x3) (.block []) (.loop (.block (body 1)) (.nonzero .x .x3)))
        (.seq (.block pow) (.seq (.loop (.block (body 8)) (.nonzero .x .x5)) tail)))
      (.block epilogue))



/-! ## With the prepared powers

`vg_ghash_prepared_aes`: `h` is byte 240 of a prepared key context
(`Spec.Gcm.PreparedPowersRepr`), whose powers `preparedPower(Hᵏ) = Hᵏ · x⁻¹`
are `H'ᵏ`, stored as `tReg k` holds them: `H'ᵏ` is at `h + powOff k`. They
are loaded instead of computed: `H'` in the prologue, `H'²` to `H'⁸` when
there are at least eight blocks. -/

/-- Where `H'ᵏ` is, from `h`: the even powers at `16 + 32 j` (`k = 2j + 2`),
the odd ones 16 bytes after (`k = 2j + 1`). -/
def powOff (k : Nat) : Nat := if k % 2 = 0 then 16 * k - 16 else 16 * k + 16

/-- `H'ᵏ` loaded, and with its halves swapped. -/
def loadPow (k : Nat) : List Instr :=
  [.ldrq (tReg k) .x0 (powOff k), .vop (.ext (sReg k) (tReg k) (tReg k) 8)]

/-- `H'` loaded, the reduction constant, and `Y`. -/
def prologueP : List Instr :=
  loadPow 1 ++ ([.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)] : List Instr) ++ loadRev Y .x1 0 ++
    ([.lsr .x .x5 .x3 3] : List Instr)

/-- `H'²` to `H'⁸` loaded. -/
def powersP : List Instr :=
  loadPow 2 ++ loadPow 3 ++ loadPow 4 ++ loadPow 5 ++ loadPow 6 ++ loadPow 7 ++ loadPow 8

def ghashP : Prog isa := ghashWith prologueP powersP

/-! ## With the powers in their own buffer

`vg_ghash_with_powers_aes` and `vg_ghash_store_powers_aes`, whose sixth
argument `pw` (`x5`) is a 128-byte buffer of the powers
(`Spec.Gcm.Powers8Repr`): `H'²ʲ⁺²` at `pw + 32 j`, `H'²ʲ⁺¹` 16 bytes after,
each as `tReg` holds it. Both have all eight powers in their registers before
the loops, whatever the number of blocks: `vg_ghash_with_powers_aes` loads
them, and `vg_ghash_store_powers_aes` computes them, as `vg_ghash_aes` does,
and stores them after its epilogue. -/

/-- GHASH from the prologue `pro`, which sets up `H'` to `H'⁸`, then `fin`
after the epilogue. Fewer than eight blocks go four, two and one at a time
(`tail`), as the last `n mod 8` do, each group with one reduction. -/
def ghashAll (pro fin : List Instr) : Prog isa :=
  .seq (.block pro)
    (.seq (.ite (.zero .x .x5) tail (.seq (.loop (.block (body 8)) (.nonzero .x .x5)) tail))
      (.block (epilogue ++ fin)))

/-- Where `H'ᵏ` is, from `pw`. -/
def pwOff (k : Nat) : Nat := if k % 2 = 0 then 16 * k - 32 else 16 * k

/-- `H'ᵏ` loaded from `pw` (`x5`), and with its halves swapped. -/
def loadPw (k : Nat) : List Instr :=
  [.ldrq (tReg k) .x5 (pwOff k), .vop (.ext (sReg k) (tReg k) (tReg k) 8)]

/-- `H'` to `H'⁸` loaded, the reduction constant, and `Y`. -/
def prologueW : List Instr :=
  loadPw 1 ++ loadPw 2 ++ loadPw 3 ++ loadPw 4 ++ loadPw 5 ++ loadPw 6 ++ loadPw 7 ++ loadPw 8 ++
    ([.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)] : List Instr) ++ loadRev Y .x1 0 ++
    ([.lsr .x .x5 .x3 3] : List Instr)

def ghashW : Prog isa := ghashAll prologueW []

/-! The powers of `vg_ghash_store_powers_aes`, which computes them for the
key setup of AES-GCM (`AesGcm::new`), with fewer instructions on the chain
that waits for `H`: the products are written rather than added to a cleared
product (`accD`), and the squares `H'²`, `H'⁴`, `H'⁶`, `H'⁸` take two
products, not four: the middle ones, `pmull(t₁, t₀)` and `pmull(t₀, t₁)`,
cancel (`sqr`). -/

/-- The four products of `acc`, of `a` and the key `t`, into `lo`, `mid` and
`hi`, written rather than added. -/
def accD (a s t : VReg) : List Instr :=
  [.vop (.pmull false HI a s), .vop (.pmull true LO a s),
   .vop (.pmull false MID a t), .vop (.pmull true T a t), .vop (.logic .eor MID MID T)]

/-- `mul`, from `accD`. -/
def mulD (d a s t : VReg) : List Instr := accD a s t ++ reduce d

/-- `reduce` of a product whose `mid` is zero. -/
def reduceS (d : VReg) : List Instr :=
  [.vop (.pmull false T LO C), .vop (.ext LO LO LO 8), .vop (.logic .eor MID LO T),
   .vop (.pmull false T MID C), .vop (.ext HI HI HI 8), .vop (.logic .eor HI HI MID),
   .vop (.ext T T T 8), .vop (.logic .eor d HI T)]

/-- `d ← mul(t, t)` with its halves swapped, `s` the halves of `t` swapped
(and the block as loaded): `lo` and `hi`, the middle products cancelling. -/
def sqr (d s : VReg) : List Instr :=
  ([.vop (.pmull false HI s s), .vop (.pmull true LO s s)] : List Instr) ++ reduceS d

/-- `H'ᵏ = mul(H'ⁱ, H'ʲ)`, a square if `i = j`, and its halves swapped. -/
def powS (k i j : Nat) : List Instr :=
  (if i = j then sqr (sReg k) (sReg i) else mulD (sReg k) (sReg i) (sReg j) (tReg j)) ++
    ([.vop (.ext (tReg k) (sReg k) (sReg k) 8)] : List Instr)

/-- `H'²` to `H'⁸`, four of them squares. -/
def powersS : List Instr :=
  powS 2 1 1 ++ powS 3 2 1 ++ powS 4 2 2 ++ powS 5 3 2 ++ powS 6 3 3 ++ powS 7 4 3 ++ powS 8 4 4

/-- `d ← H' = H · x⁻¹` from `H` as loaded in `A`, with its halves swapped, by
a shift rather than `mul(H, x⁻²)`: dividing by `x` moves each coefficient
down by one, which shifts each doubleword up by one bit (`shl`) and moves the
top bit of each into the bottom of the other (`ushr`, `ext`); the coefficient
of `x⁰` that drops out, the top bit of the low doubleword, adds
`x⁻¹ = x¹²⁷ + x⁶ + x + 1`: its `x¹²⁷` is the bit moved into the high
doubleword, the rest `0xc2 · 2⁵⁶` in the low one (the `pmull` of the bit by
the reduction constant). -/
def twist (d : VReg) : List Instr :=
  [.vop (.shift .ushr .d2 T A 63), .vop (.shift .shl .d2 LO A 1), .vop (.ext MID T T 8),
   .vop (.logic .eor LO LO MID), .vop (.pmull false HI T C), .vop (.logic .eor d LO HI)]

/-- The reduction constant in both halves of `v1`. -/
def constC : List Instr := [.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)]

/-- `vg_ghash_aes`'s prologue, with `H'` by `twist`. -/
def prologueT : List Instr :=
  loadRev A .x0 0 ++ constC ++ twist (sReg 1) ++
  ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr) ++ loadRev Y .x1 0 ++
    ([.lsr .x .x5 .x3 3] : List Instr)

/-- `pw` kept in `x8`, then the prologue, and the powers. -/
def prologueS : List Instr := ([.addImm .x .x8 .x5 0] : List Instr) ++ prologueT ++ powersS

/-- `vg_ghash_aes`, with `H'` by `twist` and the powers by `powersS`
(defined below). -/
def ghash : Prog isa := ghashWith prologueT powersS

/-- `H'ᵏ` stored to `pw` (`x8`). -/
def storePw (k : Nat) : List Instr := [.strq (tReg k) .x8 (pwOff k)]

/-- `H'` to `H'⁸` stored. -/
def storesS : List Instr :=
  storePw 1 ++ storePw 2 ++ storePw 3 ++ storePw 4 ++ storePw 5 ++ storePw 6 ++ storePw 7 ++
    storePw 8

def ghashS : Prog isa := ghashAll prologueS storesS

end VG.Impl.Gcm.AArch64.Pmull
