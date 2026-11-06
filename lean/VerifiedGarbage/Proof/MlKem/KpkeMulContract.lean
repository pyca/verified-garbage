module

public import VerifiedGarbage.Proof.MlKem.PolyContract

/-!
# ML-KEM: the arithmetic of K-PKE, a step at a time, on every target

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The contracts of three functions, each of which computes the products of
K-PKE's polynomials (§5) in one call:

* `vg_mlkem*_keygen_mul`: lines 16–18 of `K-PKE.KeyGen` (Algorithm 13),
  `ŝ = NTT(s)` and `t̂ = Â ∘ ŝ + NTT(e)`;
* `vg_mlkem*_encrypt_mul`: the products of lines 18–21 of `K-PKE.Encrypt`
  (Algorithm 14), `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)` with
  `ŷ = NTT(y)`;
* `vg_mlkem*_decrypt_mul`: the product of line 6 of `K-PKE.Decrypt`
  (Algorithm 15), `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))`.

They compose the polynomial primitives of
`Proof/MlKem/PolyContract.lean` (`vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, `vg_mlkem_inv_ntt`,
`vg_mlkem_add`) as the algorithms do, in terms of the same definitions of
`Spec/MlKem.lean` (`ntt`, `nttInv`, `dot`, `mulMatVec`, `mulMatTVec`,
`add`), so that an implementation can compute a whole step at once, and
keep its intermediate values in its own representation between the
products: the noise, the encodings and the compressions around them stay
separate calls.

They depend on the rank `k` of the parameter set, so each parameter set has
its own (`vg_mlkem768_*` and `vg_mlkem1024_*`). A vector of `R_q^k` or
`T_q^k` is its `k` polynomials one after the other, each stored as in
`PolyContract.lean` (`[u32; 256]`, reduced), and the matrix `Â` its `k²` entries by rows: `Â[i, j]` is polynomial `k i + j`
(`matAt`), as `sampleMatrix` lists them. Every function takes its
polynomials reduced and leaves them reduced. Everything is secret, and the
functions are constant time. The working space `scratch` (4 KiB) may hold
intermediate values on return, which the caller must destroy (FIPS 203
§3.3).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec VG.Spec.MlKem

/-- The vector of `k` polynomials stored from `p`, polynomial `i` at
`p + 1024 i`. -/
def vecAt (m : Mem) (p : Addr) (k : Nat) : List Poly :=
  (List.range k).map fun i => polyAt m (p + BitVec.ofNat 64 (1024 * i))

/-- The `k × k` matrix stored from `p` by rows, as its rows: `Â[i, j]` is
polynomial `k i + j`. -/
def matAt (m : Mem) (p : Addr) (k : Nat) : List (List Poly) :=
  (List.range k).map fun i => vecAt m (p + BitVec.ofNat 64 (1024 * (k * i))) k

/-- The `l` polynomials stored from `p` are reduced. -/
def VecReduced (m : Mem) (p : Addr) (l : Nat) : Prop :=
  ∀ i < l, Reduced m (p + BitVec.ofNat 64 (1024 * i))

/-- The `l` polynomials stored from `p` are `v`, reduced. -/
def VecIs (m : Mem) (p : Addr) (l : Nat) (v : List Poly) : Prop :=
  v.length = l ∧ ∀ i < l, PolyIs m (p + BitVec.ofNat 64 (1024 * i)) (v.getD i zero)

end VG.Proof.MlKem
