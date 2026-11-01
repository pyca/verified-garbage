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

/-! ## Key generation -/

/-- `t: *mut [u32; 256k], s: *mut [u32; 256k], a: *const [u32; 256k²], e: *const [u32; 256k], scratch: *mut [u64; 512]`. -/
def keygenMulSig (k : Nat) : Sig where
  params := [("t", .array true .u32 (256 * k)), ("s", .array true .u32 (256 * k)),
    ("a", .array false .u32 (256 * (k * k))), ("e", .array false .u32 (256 * k)),
    ("scratch", .array true .u64 512)]

/-- If the vectors `s` and `e` and the matrix `Â` at `a` are reduced: `s`
becomes `ŝ = NTT(s)`, and `t̂ = Â ∘ ŝ + NTT(e)` is written to `t` (lines
16–18 of Algorithm 13, `ŝ ← NTT(s)`, `ê ← NTT(e)`, `t̂ ← Â ∘ ŝ + ê`). -/
def keygenMulContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (keygenMulSig k).contract A
    (pre := fun _t s a e _scratch m =>
      VecReduced m s k ∧ VecReduced m a (k * k) ∧ VecReduced m e k)
    (post := fun t s a e _scratch m m' _ =>
      VecIs m' s k ((vecAt m s k).map ntt) ∧
      VecIs m' t k (addVec (mulMatVec (matAt m a k) ((vecAt m s k).map ntt)) ((vecAt m e k).map ntt)))
    (writeArgs := true)
    (stack := stack)

/-! ## Encryption -/

/-- `u: *mut [u32; 256(k + 1)], a: *const [u32; 256k²], t: *const [u32; 256k], y: *const [u32; 256k], scratch: *mut [u64; 512]`. -/
def encryptMulSig (k : Nat) : Sig where
  params := [("u", .array true .u32 (256 * (k + 1))), ("a", .array false .u32 (256 * (k * k))),
    ("t", .array false .u32 (256 * k)), ("y", .array false .u32 (256 * k)),
    ("scratch", .array true .u64 512)]

/-- If the matrix `Â` at `a` and the vectors `t̂` at `t` and `y` at `y` are
reduced: writes `NTT⁻¹(Â^⊺ ∘ ŷ)` (`k` polynomials) and then
`NTT⁻¹(t̂^⊺ ∘ ŷ)` to `u`, with `ŷ = NTT(y)` (the products of lines 18, 19
and 21 of Algorithm 14). -/
def encryptMulContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptMulSig k).contract A
    (pre := fun _u a t y _scratch m =>
      VecReduced m a (k * k) ∧ VecReduced m t k ∧ VecReduced m y k)
    (post := fun u a t y _scratch m m' _ =>
      VecIs m' u (k + 1)
        (((mulMatTVec k (matAt m a k) ((vecAt m y k).map ntt)).map nttInv) ++
          [nttInv (dot (vecAt m t k) ((vecAt m y k).map ntt))]))
    (writeArgs := true)
    (stack := stack)

/-! ## Decryption -/

/-- `w: *mut [u32; 256], s: *const [u32; 256k], u: *const [u32; 256k], scratch: *mut [u64; 512]`. -/
def decryptMulSig (k : Nat) : Sig where
  params := [("w", .array true .u32 256), ("s", .array false .u32 (256 * k)),
    ("u", .array false .u32 (256 * k)), ("scratch", .array true .u64 512)]

/-- If the vectors `ŝ` at `s` and `u'` at `u` are reduced: writes
`NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` to `w` (the product of line 6 of Algorithm 15). -/
def decryptMulContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (decryptMulSig k).contract A
    (pre := fun _w s u _scratch m => VecReduced m s k ∧ VecReduced m u k)
    (post := fun w s u _scratch m m' _ =>
      PolyIs m' w (nttInv (dot (vecAt m s k) ((vecAt m u k).map ntt))))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.MlKem
