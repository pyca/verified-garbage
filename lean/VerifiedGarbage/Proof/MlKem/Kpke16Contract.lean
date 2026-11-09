module

public import VerifiedGarbage.Proof.MlKem.KpkeMulContract

/-!
# ML-KEM with 16-bit coefficients: K-PKE in one call, on every target

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

These contracts store polynomials in 16 bits per coefficient, in place of
the 32 bits of `PolyContract.lean` and `KpkeMulContract.lean`. They are
written for
the storage width `w` of a coefficient (`polyAtW w`, `ReducedW w`, …), and
the contracts here take `w = 16`. `polyAt` and its family are the case
`w = 32`.

A polynomial is stored as `[u16; 256]`: coefficient `i` is the
little-endian `u16` at byte `2i`. It is less than `q` (`ReducedW 16`), so
it is the integer that represents its element of `ℤ_q` (`polyAtW 16`). A
vector of `k` polynomials is stored one polynomial after the other
(`vecAtW 16`, 512 bytes each). The matrix `Â` is stored by rows, so
`Â[i, j]` is polynomial `k i + j` (`matAtW 16`), in the order
`sampleMatrix` lists them.

The functions are:

* `vg_mlkem16_sample_ntt`, `vg_mlkem16_sample_ntt4` and `vg_mlkem16_cbd2`:
  the samplers of `PolyContract.lean`, writing 16-bit coefficients.
* `vg_mlkem*_kpke_keygen`, `vg_mlkem*_kpke_encrypt` and
  `vg_mlkem*_kpke_decrypt`, for each parameter set: all of K-PKE
  (Algorithms 13–15) but the sampling, in one call each.
  * They take the matrix `Â` and the noise as sampled.
  * They take keys and ciphertexts as bytes, in and out.
  * So an implementation keeps every intermediate value in its own
    representation, from the NTTs to the encodings and compressions.

Everything is secret, and the functions are constant time, but for the
samplers' seeds, which are public in ML-KEM and may leak (as in
`PolyContract.lean`). Functions with working space `scratch` may leave intermediate
values in it, and so may the K-PKE functions in the noise they take
(`se`, `r`), which they may overwrite. The caller must destroy those values
(FIPS 203 §3.3). The functions may overwrite their arguments passed in
memory, where the calling convention allows it (`writeArgs`). Each takes
the number of bytes of stack below the stack pointer that its calls and
frames use (`stack`, see `Sig.contract`), which depends on the target.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec VG.Spec.MlKem
open Sha3 (bytesAt)

/-! ## Polynomials stored with `w`-bit coefficients -/

/-- The `w`-bit coefficient `i` of the polynomial stored at `p`, a multiple
of 8 bits wide: the little-endian `w / 8` bytes from `p + (w / 8) i`. -/
def coeffAtW (w : Nat) (m : Mem) (p : Addr) (i : Nat) : BitVec w :=
  m.readW (p + BitVec.ofNat 64 (w / 8 * i)) w

/-- The polynomial stored with `w`-bit coefficients at `p`: coefficient `i`
is `coeffAtW w m p i`, modulo `q`. -/
def polyAtW (w : Nat) (m : Mem) (p : Addr) : Poly :=
  Vector.ofFn fun i => ofNat (coeffAtW w m p i.val).toNat

/-- The polynomial stored with `w`-bit coefficients at `p` is reduced: each
coefficient is less than `q`, so it is the integer that represents its
element of `ℤ_q`. -/
def ReducedW (w : Nat) (m : Mem) (p : Addr) : Prop := ∀ i < n, (coeffAtW w m p i).toNat < q

/-- `f` is stored with `w`-bit coefficients at `p`, reduced. -/
def PolyIsW (w : Nat) (m : Mem) (p : Addr) (f : Poly) : Prop := ReducedW w m p ∧ polyAtW w m p = f

/-- The vector of `k` polynomials stored with `w`-bit coefficients from `p`:
polynomial `i` at `p + 32 w i` (each takes `256 w / 8` bytes). -/
def vecAtW (w : Nat) (m : Mem) (p : Addr) (k : Nat) : List Poly :=
  (List.range k).map fun i => polyAtW w m (p + BitVec.ofNat 64 (32 * w * i))

/-- The `k × k` matrix stored with `w`-bit coefficients from `p`, by rows,
as its rows: `Â[i, j]` is polynomial `k i + j`. -/
def matAtW (w : Nat) (m : Mem) (p : Addr) (k : Nat) : List (List Poly) :=
  (List.range k).map fun i => vecAtW w m (p + BitVec.ofNat 64 (32 * w * (k * i))) k

/-- The `l` polynomials stored with `w`-bit coefficients from `p` are
reduced. -/
def VecReducedW (w : Nat) (m : Mem) (p : Addr) (l : Nat) : Prop :=
  ∀ i < l, ReducedW w m (p + BitVec.ofNat 64 (32 * w * i))

end VG.Proof.MlKem
