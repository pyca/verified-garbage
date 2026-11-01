module

public import VerifiedGarbage.Proof.MlKem.Kpke16Contract

/-!
# ML-KEM with 16-bit coefficients: K-PKE key generation a row at a time

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The contracts of two functions that together compute what
`vg_mlkem*_kpke_keygen` (`Kpke16Contract.lean`) does in one call, so that a caller can encode each row of `t̂` as soon as the matrix
`Â` has its row (for instance to hash `ek` while it samples the rest of
`Â`):

* `vg_mlkem*_kpke_keygen_ntt`: lines 16, 17 and 20 of `K-PKE.KeyGen`
  (Algorithm 13) but for `t̂`: `ŝ ← NTT(s)` and `ê ← NTT(e)`, from `s` and
  `e` stored with 16 bits, and `ByteEncode₁₂(ŝ)`, which is `dk_PKE`;
* `vg_mlkem*_kpke_keygen_row`: lines 18 and 19 for row `i` of `t̂`:
  `ByteEncode₁₂(Â[i] ∘ ŝ + ê[i])`, the 384 bytes of `ek_PKE` from `384 i`.

Between the two, `ŝ` and `ê` are vectors of polynomials of `u32`s
(`vecAt`, `KpkeMulContract.lean`), reduced; a row of `Â` is `k`
polynomials of `u16`s (`vecAtW 16`), as `matAtW 16` stores it. Everything is
secret, and the functions are constant time. The working space `scratch`
(4 KiB) may hold intermediate values on return, and the row function may
overwrite `ê[i]`; the caller must destroy those values (FIPS 203 §3.3).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec VG.Spec.MlKem
open Sha3 (bytesAt)

/-- `dk: *mut [u8; 384k], s: *mut [u32; 256k], e: *mut [u32; 256k], se: *const [u16; 512k], scratch: *mut [u64; 512]`. -/
def kpkeKeyGenNttSig (k : Nat) : Sig where
  params := [("dk", .array true .u8 (384 * k)), ("s", .array true .u32 (256 * k)),
    ("e", .array true .u32 (256 * k)), ("se", .array false .u16 (512 * k)),
    ("scratch", .array true .u64 512)]

/-- Lines 16, 17 and 20 of `K-PKE.KeyGen` (Algorithm 13) for the vectors `s`
and `e` reduced at `se`, one after the other: writes `ŝ = NTT(s)` to `s`,
`ê = NTT(e)` to `e`, and `ByteEncode₁₂(ŝ)` (all of `dk_PKE`) to `dk`. -/
def kpkeKeyGenNttContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (kpkeKeyGenNttSig k).contract A
    (pre := fun _dk _s _e se _scratch m => VecReducedW 16 m se (2 * k))
    (post := fun dk s e se _scratch m m' _ =>
      let ŝ := (vecAtW 16 m se k).map ntt
      VecIs m' s k ŝ ∧ VecIs m' e k ((vecAtW 16 m (se + BitVec.ofNat 64 (512 * k)) k).map ntt) ∧
        bytesAt m' dk (384 * k) = encodeVec ŝ)
    (writeArgs := true)
    (stack := stack)

/-- `ek: *mut [u8; 384], a: *const [u16; 256k], s: *const [u32; 256k], e: *mut [u32; 256], scratch: *mut [u64; 512]`. -/
def kpkeKeyGenRowSig (k : Nat) : Sig where
  params := [("ek", .array true .u8 384), ("a", .array false .u16 (256 * k)),
    ("s", .array false .u32 (256 * k)), ("e", .array true .u32 256),
    ("scratch", .array true .u64 512)]

/-- Lines 18 and 19 of `K-PKE.KeyGen` (Algorithm 13) for one row of `t̂`,
with the row `Â[i]` reduced at `a`, `ŝ` reduced at `s` and `ê[i]` reduced at
`e`: writes `ByteEncode₁₂(Â[i] ∘ ŝ + ê[i])` to `ek`. -/
def kpkeKeyGenRowContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (kpkeKeyGenRowSig k).contract A
    (pre := fun _ek a s e _scratch m => VecReducedW 16 m a k ∧ VecReduced m s k ∧ Reduced m e)
    (post := fun ek a s e _scratch m m' _ =>
      bytesAt m' ek 384 = encode12 (add (dot (vecAtW 16 m a k) (vecAt m s k)) (polyAt m e)))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.MlKem
