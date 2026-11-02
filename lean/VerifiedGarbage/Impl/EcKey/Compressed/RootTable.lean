module

public import VerifiedGarbage.Spec.P224

/-!
# A square root by a table of powers of a generator of the 2-Sylow subgroup

For a prime with `p - 1 = q 16ⁿ`, `q` odd, and `c` of order `16ⁿ` (a power
`z^q` of a nonresidue `z`), a root of `a` is found from `w = a^((q-1)/2)`,
`r = w a` and `t = w r = a^q` by finding `k < 16ⁿ` with `t c^k = 1`, a
base-16 digit at a time from the lowest, with the table `T m d = c^(d 16^m)`
(`m < n`, `d < 16`) of the code's constants:

* with `s m = t^(16^m)`, digit `j` is read from
  `y = s (n-1-j) · Π_{i<j} T (n-1-j+i) dᵢ` (`tacc`), which is `g^(-dⱼ)` for
  `g = c^(16^(n-1))`, of order 16, whose powers are the last row of the
  table: `dⱼ = (16 - e) mod 16` for the entry `g^e` equal to `y`, summed over
  the entries (`digAcc`; there is one when `a` is a nonzero square);
* the root is `r c^(k/2) = r Π_i T i eᵢ` for the digits `eᵢ` of `k / 2`.

The caller checks the candidate's square, so a nonsquare may give anything.
Every step is a function of `a`, which is public: the code may look up the
table at the digits. P-224's instance (`root224`): `p - 1 = (2^128 - 1) 16^24`,
`c = 11^q`.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed

open Spec.Weierstrass

variable {p : Nat} [NeZero p]

/-- `y` times `T (o + i) dᵢ` for the base-16 digits `dᵢ` of `k`, `i < j`, in
order. -/
def tacc (T : Nat → Nat → Fin p) (o k : Nat) (y : Fin p) : Nat → Fin p
  | 0 => y
  | j + 1 => tacc T o k y j * T (o + j) (k / 16 ^ j % 16)

/-- The sum of `(16 - e) mod 16` over the entries `e < f` of `G` equal to `y`. -/
def digAcc (G : Nat → Fin p) (y : Fin p) : Nat → Nat
  | 0 => 0
  | f + 1 => digAcc G y f + if y = G f then (16 - f) % 16 else 0

/-- The number of the first `j` digits, from `s m = t^(16^m)`. -/
def kGo (T : Nat → Nat → Fin p) (s : Nat → Fin p) (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let k := kGo T s n j
    k + digAcc (T (n - 1)) (tacc T (n - 1 - j) k (s (n - 1 - j)) j) 16 % 16 * 16 ^ j

/-- The candidate root of `a`, for `p - 1 = q 16ⁿ` and the table `T`. -/
def rootTable (a : Fin p) (q n : Nat) (T : Nat → Nat → Fin p) : Fin p :=
  let w := pow a ((q - 1) / 2)
  let r := w * a
  let t := w * r
  tacc T 0 (kGo T (fun m => pow t (16 ^ m)) n n / 2) r n

/-! ## P-224 -/

/-- The odd part `q` of `p - 1 = q 2⁹⁶`. -/
def q224 : Nat := (Spec.P224.p - 1) / 2 ^ 96

/-- `c = 11^q`, of order `2⁹⁶`. -/
def c224 : Fin Spec.P224.curve.p := pow (Fin.ofNat Spec.P224.curve.p 11) q224

/-- The table: `c^(d 16^m)`. -/
def tbl224 (m d : Nat) : Fin Spec.P224.curve.p := pow c224 (d * 16 ^ m)

/-- P-224's candidate root. -/
def root224 (a : Fin Spec.P224.curve.p) : Fin Spec.P224.curve.p := rootTable a q224 24 tbl224

end VG.Impl.EcKey.Compressed
