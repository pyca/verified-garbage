/-!
# The primes below 8162, by a sieve on one number

The candidates' trial division (`Spec.RsaKeyGen.obviouslyComposite`) divides
by the first 1024 primes, the primes below 8162. The specification finds
them by trial division of every number, which the kernel cannot evaluate in
reasonable time; here the composites below 8162 are the set bits of one
number, the multiples `d k` (`2 ≤ d ≤ 90`, `k ≥ 2`) or'ed together, which the
kernel computes with its arithmetic on numbers. `Proof/RsaKeyGen/Primes.lean`
proves that `primes` is `Spec.RsaKeyGen.smallPrimes`.

The candidates' table of divisors (`slots`, packed four to a word by
`tabWord`) is the same on every target.
-/

namespace VG.Impl.RsaKeyGen

/-- The multiples `d k` below 8162 with `k ≥ 2`, as set bits. -/
def multMask (d : Nat) : Nat :=
  (List.range (8162 / d + 1)).foldl (fun m k => if 2 ≤ k then m ||| 2 ^ (d * k) else m) 0

/-- The composites below 8162 (and some numbers above), as set bits: every
composite below `91² = 8281` has a factor from 2 to 90. -/
def compMask : Nat := (List.range 91).foldl (fun m d => if 2 ≤ d then m ||| multMask d else m) 0

/-- The primes below 8162. -/
def primes : List Nat := (List.range 8162).filter fun n => 2 ≤ n && !compMask.testBit n

/-! ## The candidates' table -/

/-- The table's 1024 entries: the primes 3 to 3671 (the 2nd to the 512th),
3, then the primes 3673 to 8161 (the 513th to the 1024th). -/
def slots : List Nat := (primes.take 512).drop 1 ++ [3] ++ primes.drop 512

/-- Entry `i` of the table. -/
def tabEntry (i : Nat) : Nat := slots.getD i 0

/-- Word `i` of the table: entries `4 i` to `4 i + 3`, 16 bits each, the first
the least significant. -/
def tabWord (i : Nat) : Nat :=
  tabEntry (4 * i) + tabEntry (4 * i + 1) * 2 ^ 16 + tabEntry (4 * i + 2) * 2 ^ 32 + tabEntry (4 * i + 3) * 2 ^ 48

end VG.Impl.RsaKeyGen
