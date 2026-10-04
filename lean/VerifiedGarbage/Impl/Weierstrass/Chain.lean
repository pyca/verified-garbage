import VerifiedGarbage.Impl.Mont.Mod

/-!
# Powers by sliding windows, on any target

`x^e` for an exponent `e` known when the code is generated (`p - 2` and
`n - 2`, for inverses by Fermat's little theorem), by a chain of squarings
and multiplications by odd powers `x^1, x^3, …, x^15`: `slide e` reads `e`'s
bits from the top in windows of at most four bits that end in a one, giving
the first window `d₀` and steps `(s, d)`: square `s` times, then multiply by
`x^d` (`d` odd, or `0` for none). The steps' value from `d₀` is `e`
(`chainVal`), which the proofs check for each exponent.
-/

namespace VG.Impl.Weierstrass

open VG.Impl.Mont

/-- The value of the steps from `v`: `v 2^s + d` for each step `(s, d)`. -/
def chainVal (v : Nat) : List (Nat × Nat) → Nat
  | [] => v
  | (s, d) :: rest => chainVal (v * 2 ^ s + d) rest

/-- The low `f` bits of `e` up to its top one, from the bottom. -/
def bitsLSB : Nat → Nat → List Bool
  | 0, _ => []
  | f + 1, e => if e = 0 then [] else (e % 2 = 1) :: bitsLSB f (e / 2)

/-- The bits of `e < 2^1024`, from the top one down. -/
def bitsMSB (e : Nat) : List Bool := (bitsLSB 1024 e).reverse

/-- The window starting at a one: at most four bits, ending in a one; its length,
its value and the bits after it. -/
def window (bs : List Bool) : Nat × Nat × List Bool :=
  let w := ((bs.take 4).reverse.dropWhile (· = false)).reverse
  (w.length, w.foldl (fun a b => 2 * a + b.toNat) 0, bs.drop w.length)

/-- The steps for the bits `bs`, after `z` squarings not yet made. -/
def slideGo : Nat → Nat → List Bool → List (Nat × Nat)
  | 0, z, _ => if z = 0 then [] else [(z, 0)]
  | _ + 1, z, [] => if z = 0 then [] else [(z, 0)]
  | f + 1, z, false :: bs => slideGo f (z + 1) bs
  | f + 1, z, true :: bs =>
    let (l, v, rest) := window (true :: bs)
    (z + l, v) :: slideGo f 0 rest

/-- The first window and the steps of `e`. -/
def slide (e : Nat) : Nat × List (Nat × Nat) :=
  let (_, v, rest) := window (bitsMSB e)
  (v, slideGo (rest.length + 1) 0 rest)

/-- What a power by a chain needs: the modulus, the slots of the result and
of the base, and of the table: `x^(2 i + 1)` at slot `i < 8`, `x²` at slot
`8`, slots of `8 n` bytes from `tbl`; and the chain. -/
structure ChainCfg where
  M : Mod
  acc : Nat
  base : Nat
  tbl : Nat
  first : Nat
  steps : List (Nat × Nat)

/-- Slot `i` of the table. -/
def ChainCfg.slot (P : ChainCfg) (i : Nat) : Nat := P.tbl + 8 * P.M.n * i

/-- The chain of `e`. -/
def ChainCfg.ofExp (M : Mod) (acc base tbl e : Nat) : ChainCfg :=
  ⟨M, acc, base, tbl, (slide e).1, (slide e).2⟩

end VG.Impl.Weierstrass
