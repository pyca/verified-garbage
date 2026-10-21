module

public import VerifiedGarbage.Spec.MlKem.Kpke16

/-!
# ML-KEM with 16-bit coefficients: K-PKE key generation a row at a time

**Trusted** (as every file in `Spec/`). The contracts of two functions that
together compute what `vg_mlkem*_kpke_keygen` (`Kpke16.lean`) does in one
call, so that a caller can encode each row of `t̂` as soon as the matrix
`Â` has its row (for instance to hash `ek` while it samples the rest of
`Â`):

* `vg_mlkem*_kpke_keygen_ntt`: lines 16, 17 and 20 of `K-PKE.KeyGen`
  (Algorithm 13) but for `t̂`: `ŝ ← NTT(s)` and `ê ← NTT(e)`, from `s` and
  `e` stored with 16 bits, and `ByteEncode₁₂(ŝ)`, which is `dk_PKE`;
* `vg_mlkem*_kpke_keygen_row`: lines 18 and 19 for row `i` of `t̂`:
  `ByteEncode₁₂(Â[i] ∘ ŝ + ê[i])`, the 384 bytes of `ek_PKE` from `384 i`.

Between the two, `ŝ` and `ê` are vectors of polynomials of `u32`s
(`vecAt`, `Spec/MlKem/KpkeMul.lean`), reduced; a row of `Â` is `k`
polynomials of `u16`s (`vecAtW 16`), as `matAtW 16` stores it. Everything is
secret, and the functions are constant time. The working space `scratch`
(4 KiB) may hold intermediate values on return, and the row function may
overwrite `ê[i]`; the caller must destroy those values (FIPS 203 §3.3).
-/

@[expose] public section

namespace VG.Spec.MlKem

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

/-- `vg_mlkem*_kpke_keygen_ntt` of the parameter set `p` on every target, with
`kpkeKeyGenNttContract p.k`. -/
def Params.kpkeKeyGenNttApi (p : Params) : Api where
  module := p.module
  name := p.fn "kpke_keygen_ntt"
  sig := kpkeKeyGenNttSig p.k
  writeArgs := true
  contracts := some fun A stack => kpkeKeyGenNttContract p.k A stack
  summary := s!"The transforms of {p.name} K-PKE key generation (FIPS 203 Algorithm 13, lines \
    16, 17 and 20). The input is the vectors `s` and `e` in `*se` ({p.k} polynomials each, one \
    after the other, 256 `u16` coefficients reduced modulo `q` = 3329). Writes `ŝ = NTT(s)` to \
    `*s`, `ê = NTT(e)` to `*e` ({p.k} polynomials of 256 `u32` coefficients each, reduced), \
    and `ByteEncode₁₂(ŝ)` to `*dk`.\n\n\
    Contract: `VG.Spec.MlKem.kpkeKeyGenNttContract`. Constant time: only the pointers may \
    affect timing."
  safety := [reduced16Safety "se" (2 * p.k), mulScratchDoc]

/-- `vg_mlkem*_kpke_keygen_row` of the parameter set `p` on every target, with
`kpkeKeyGenRowContract p.k`. -/
def Params.kpkeKeyGenRowApi (p : Params) : Api where
  module := p.module
  name := p.fn "kpke_keygen_row"
  sig := kpkeKeyGenRowSig p.k
  writeArgs := true
  contracts := some fun A stack => kpkeKeyGenRowContract p.k A stack
  summary := s!"A row of `t̂` in {p.name} K-PKE key generation (FIPS 203 Algorithm 13, lines \
    18 and 19). The inputs are the row `Â[i]` of the matrix in `*a` ({p.k} polynomials of 256 \
    `u16` coefficients), and `ŝ` in `*s` ({p.k} polynomials) and `ê[i]` in `*e` of 256 `u32` \
    coefficients each, all reduced modulo `q` = 3329. Writes `ByteEncode₁₂(Â[i] ∘ ŝ + ê[i])` \
    to `*ek`.\n\n\
    Contract: `VG.Spec.MlKem.kpkeKeyGenRowContract`. Constant time: only the pointers may \
    affect timing."
  safety := [reduced16Safety "a" p.k, s!"Each of the {256 * p.k} `u32`s of `s` and the 256 of \
    `e` must be less than 3329.", noiseSafety "e", mulScratchDoc]

/-- `vg_mlkem768_kpke_keygen_ntt` on every target. -/
def kpkeKeyGenNttApi : Api := mlKem768.kpkeKeyGenNttApi
/-- `vg_mlkem768_kpke_keygen_row` on every target. -/
def kpkeKeyGenRowApi : Api := mlKem768.kpkeKeyGenRowApi

end VG.Spec.MlKem
