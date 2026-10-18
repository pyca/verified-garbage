module

public import VerifiedGarbage.Spec.MlKem.KpkeMul

/-!
# ML-KEM with 16-bit coefficients: K-PKE in one call, on every target

**Trusted** (as every file in `Spec/`). These contracts store polynomials
in 16 bits per coefficient, in place of the 32 bits of
`Spec/MlKem/Poly.lean` and `Spec/MlKem/KpkeMul.lean`. They are written for
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
  the samplers of `Poly.lean`, writing 16-bit coefficients.
* `vg_mlkem*_kpke_keygen`, `vg_mlkem*_kpke_encrypt` and
  `vg_mlkem*_kpke_decrypt`, for each parameter set: all of K-PKE
  (Algorithms 13–15) but the sampling, in one call each.
  * They take the matrix `Â` and the noise as sampled.
  * They take keys and ciphertexts as bytes, in and out.
  * So an implementation keeps every intermediate value in its own
    representation, from the NTTs to the encodings and compressions.

Everything is secret, and the functions are constant time, but for the
samplers' seeds, which are public in ML-KEM and may leak (as in
`Poly.lean`). Functions with working space `scratch` may leave intermediate
values in it, and so may the K-PKE functions in the noise they take
(`se`, `r`), which they may overwrite. The caller must destroy those values
(FIPS 203 §3.3). The functions may overwrite their arguments passed in
memory, where the calling convention allows it (`writeArgs`). Each takes
the number of bytes of stack below the stack pointer that its calls and
frames use (`stack`, see `Sig.contract`), which depends on the target.
-/

@[expose] public section

namespace VG.Spec.MlKem

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

/-! ## Sampling -/

/-- `vg_mlkem16_sample_ntt(seed: *const [u8; 34], a: *mut [u16; 256], scratch: *mut [u64; 256]) -> u32`. -/
def sampleNTT16Sig : Sig where
  params := [("seed", .array false .u8 34), ("a", .array true .u16 256),
    ("scratch", .array true .u64 256)]
  ret := some .u32

/-- With the 34 bytes `B` at `seed`: writes `SampleNTT(B)` (Algorithm 7) to
`a` with 16-bit coefficients, reduced, and returns 1; or returns 0 (see
`Outcome`), and `a` is unspecified. May leak `B`. -/
def sampleNTT16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sampleNTT16Sig.contract A
    (post := fun seed a _scratch m m' r =>
      (r = 1 → ReducedW 16 m' a) ∧
        Outcome (fun iters => sampleNTT iters (bytesAt m seed 34)) r (polyAtW 16 m' a))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _a _scratch m => (bytesAt m seed 34).map (·.toNat))

/-- `vg_mlkem16_sample_ntt4(seeds: *const [u8; 136], a: *mut [u16; 1024], scratch: *mut [u64; 1024]) -> u32`. -/
def sampleNTT4_16Sig : Sig where
  params := [("seeds", .array false .u8 136), ("a", .array true .u16 1024),
    ("scratch", .array true .u64 1024)]
  ret := some .u32

/-- Polynomial `k` of four with 16-bit coefficients at `a`: from byte
`512 k`. -/
def poly4_16 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (512 * k)

/-- `SampleNTT` four times: with the four 34-byte seeds `B₀, …, B₃` at
`seeds` (`seed4`), writes `SampleNTT(Bₖ)` (Algorithm 7) to the polynomial
at `a + 512 k` (`poly4_16`) with 16-bit coefficients, reduced, for each `k`,
and returns 1. Or returns 0 if the loop of `SampleNTT` reaches its bound
(`minIterations`) for one of them, and `a` is unspecified. May leak the
seeds. -/
def sampleNTT4_16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sampleNTT4_16Sig.contract A
    (post := fun seeds a _scratch m m' r =>
      (r = 1 → ∀ k < 4, ReducedW 16 m' (poly4_16 a k)) ∧
        ((r = 1 ∧ ∀ k < 4, ∃ iters,
            sampleNTT iters (seed4 m seeds k) = some (polyAtW 16 m' (poly4_16 a k))) ∨
          (r = 0 ∧ ∃ k < 4, sampleNTT minIterations (seed4 m seeds k) = none)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seeds _a _scratch m => (bytesAt m seeds 136).map (·.toNat))

/-- `vg_mlkem16_cbd2(b: *const [u8; 128], f: *mut [u16; 256])`. -/
def cbd2_16Sig : Sig where
  params := [("b", .array false .u8 128), ("f", .array true .u16 256)]

/-- Writes `SamplePolyCBD₂(B)` (Algorithm 8, `η = 2`) of the 128 bytes `B`
at `b` to `f` with 16-bit coefficients, reduced. -/
def cbd2_16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbd2_16Sig.contract A
    (post := fun b f m m' _ => PolyIsW 16 m' f (samplePolyCBD 2 (bytesAt m b 128)))
    (writeArgs := true)
    (stack := stack)

/-! ## K-PKE -/

/-- `ek: *mut [u8; 384k], dk: *mut [u8; 384k], a: *const [u16; 256k²], se: *mut [u16; 512k], scratch: *mut [u64; 2560]`. -/
def kpkeKeyGenSig (k : Nat) : Sig where
  params := [("ek", .array true .u8 (384 * k)), ("dk", .array true .u8 (384 * k)),
    ("a", .array false .u16 (256 * (k * k))), ("se", .array true .u16 (512 * k)),
    ("scratch", .array true .u64 2560)]

/-- Lines 16–20 of `K-PKE.KeyGen` (Algorithm 13), with the matrix `Â`
reduced at `a` and the vectors `s` and `e` reduced at `se`, one after the
other. Writes `ByteEncode₁₂(t̂)` to `ek` and `ByteEncode₁₂(ŝ)` to `dk`, with
`ŝ ← NTT(s)`, `ê ← NTT(e)` and `t̂ ← Â ∘ ŝ + ê`. These are the first
`384k` bytes of `ek_PKE` and all of `dk_PKE`. -/
def kpkeKeyGenContract (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (kpkeKeyGenSig k).contract A
    (pre := fun _ek _dk a se _scratch m =>
      VecReducedW 16 m a (k * k) ∧ VecReducedW 16 m se (2 * k))
    (post := fun ek dk a se _scratch m m' _ =>
      let ŝ := (vecAtW 16 m se k).map ntt
      let ê := (vecAtW 16 m (se + BitVec.ofNat 64 (512 * k)) k).map ntt
      bytesAt m' ek (384 * k) = encodeVec (addVec (mulMatVec (matAtW 16 m a k) ŝ) ê) ∧
        bytesAt m' dk (384 * k) = encodeVec ŝ)
    (writeArgs := true)
    (stack := stack)

/-- `ct: *mut [u8; ctLen], a: *const [u16; 256k²], t: *const [u8; 384k], r: *mut [u16; 256(2k + 1)], m: *const [u8; 32], scratch: *mut [u64; 2560]`. -/
def Params.kpkeEncryptSig (p : Params) : Sig where
  params := [("ct", .array true .u8 p.ctLen), ("a", .array false .u16 (256 * (p.k * p.k))),
    ("t", .array false .u8 (384 * p.k)), ("r", .array true .u16 (256 * (2 * p.k + 1))),
    ("m", .array false .u8 32), ("scratch", .array true .u64 2560)]

/-- Lines 2 and 18–23 of `K-PKE.Encrypt` (Algorithm 14), after sampling. The
inputs are:
* the matrix `Â` reduced at `a`;
* the bytes of `t̂` at `t` (the first `384k` bytes of `ek_PKE`, decoded as
  on line 2, modulo `q`);
* the vectors `y` and `e₁` and the polynomial `e₂`, reduced, one after the
  other at `r`;
* the message at `m`.

Writes the ciphertext `c = c₁ ‖ c₂` to `ct`, as `kpkeEncrypt` computes it:
`ŷ ← NTT(y)`, `u ← NTT⁻¹(Â^⊺ ∘ ŷ) + e₁`, `μ ← Decompress₁(ByteDecode₁(m))`,
`v ← NTT⁻¹(t̂^⊺ ∘ ŷ) + e₂ + μ`, `c₁ ← ByteEncode_{d_u}(Compress_{d_u}(u))`
and `c₂ ← ByteEncode_{d_v}(Compress_{d_v}(v))`. -/
def Params.kpkeEncryptContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) :
    Contract M :=
  p.kpkeEncryptSig.contract A
    (pre := fun _ct a _t r _msg _scratch m =>
      VecReducedW 16 m a (p.k * p.k) ∧ VecReducedW 16 m r (2 * p.k + 1))
    (post := fun ct a t r msg _scratch m m' _ =>
      let tHat := decodeVec p.k (bytesAt m t (384 * p.k))
      let ŷ := (vecAtW 16 m r p.k).map ntt
      let e₁ := vecAtW 16 m (r + BitVec.ofNat 64 (512 * p.k)) p.k
      let e₂ := polyAtW 16 m (r + BitVec.ofNat 64 (1024 * p.k))
      let u := addVec ((mulMatTVec p.k (matAtW 16 m a p.k) ŷ).map nttInv) e₁
      let μ := decodeDecompress 1 (bytesAt m msg 32)
      let v := add (add (nttInv (dot tHat ŷ)) e₂) μ
      bytesAt m' ct p.ctLen = u.flatMap (compressEncode p.du) ++ compressEncode p.dv v)
    (writeArgs := true)
    (stack := stack)

/-- `m: *mut [u8; 32], s: *const [u8; 384k], ct: *const [u8; ctLen], scratch: *mut [u64; 2048]`. -/
def Params.kpkeDecryptSig (p : Params) : Sig where
  params := [("m", .array true .u8 32), ("s", .array false .u8 (384 * p.k)),
    ("ct", .array false .u8 p.ctLen), ("scratch", .array true .u64 2048)]

/-- `K-PKE.Decrypt` (Algorithm 15): writes `kpkeDecrypt` of the decryption
key `dk_PKE` at `s` (`384k` bytes, decoded modulo `q`) and the ciphertext
at `ct` to `m`. -/
def Params.kpkeDecryptContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) :
    Contract M :=
  p.kpkeDecryptSig.contract A
    (post := fun msg s ct _scratch m m' _ =>
      bytesAt m' msg 32 = kpkeDecrypt p (bytesAt m s (384 * p.k)) (bytesAt m ct p.ctLen))
    (writeArgs := true)
    (stack := stack)

/-! ## The functions on every target -/

/-- The `# Safety` item of `count` polynomials of 16-bit coefficients at
`name`, which must be reduced. -/
def reduced16Safety (name : String) (count : Nat) : String :=
  s!"Each of the {256 * count} `u16`s of `{name}` must be less than 3329."

/-- The `# Safety` item of noise that the function may overwrite. -/
def noiseSafety (name : String) : String :=
  s!"`{name}` is working space too: on return it may hold intermediate values, which the \
    caller must destroy (FIPS 203 §3.3)."

/-- `vg_mlkem16_sample_ntt` on every target. -/
def sampleNTT16Api : Api where
  module := "mlkem16"
  name := "vg_mlkem16_sample_ntt"
  sig := sampleNTT16Sig
  writeArgs := true
  contracts := some fun A stack => sampleNTT16Contract A stack
  summary := "`SampleNTT` (FIPS 203 Algorithm 7): writes the element of `T_q` sampled from the \
    SHAKE128 output of the 34 bytes `*seed` to `*a` (256 coefficients less than `q` = 3329), \
    and returns 1. Returns 0 if the loop reaches its bound, which is at least 280 iterations \
    (FIPS 203 Appendix B; this happens with probability less than 2^-261): `*a` is then \
    unspecified, and the caller must destroy it and treat the operation as failed.\n\n\
    Contract: `VG.Spec.MlKem.sampleNTT16Contract`. Not constant time in the seed: timing may \
    depend on the pointer and on `*seed` (public in ML-KEM: the seed `ρ` of the matrix and two \
    indices), but not on anything else."
  safety := [scratchSafety]

/-- `vg_mlkem16_sample_ntt4` on every target. -/
def sampleNTT4_16Api : Api where
  module := "mlkem16"
  name := "vg_mlkem16_sample_ntt4"
  sig := sampleNTT4_16Sig
  writeArgs := true
  contracts := some fun A stack => sampleNTT4_16Contract A stack
  summary := "`SampleNTT` (FIPS 203 Algorithm 7) four times: for each `k` < 4, writes the element of \
    `T_q` sampled from the SHAKE128 output of the 34 bytes of `*seeds` from byte `34 k` to the \
    256 coefficients of `*a` from coefficient `256 k` (each less than `q` = 3329), and returns 1. \
    Returns 0 if the loop reaches its bound for one of them, which is at least 280 iterations \
    (FIPS 203 Appendix B; this happens with probability less than 2^-261 for each): `*a` is \
    then unspecified, and the caller must destroy it and treat the operation as failed. The \
    four are independent, so an implementation may compute them together (e.g. four SHAKE128 \
    instances at once in vector registers).\n\n\
    Contract: `VG.Spec.MlKem.sampleNTT4_16Contract`. Not constant time in the seeds: timing may \
    depend on the pointer and on `*seeds` (public in ML-KEM: the seed `ρ` of the matrix and \
    indices), but not on anything else."
  safety := [scratchSafety]

/-- `vg_mlkem16_cbd2` on every target. -/
def cbd2_16Api : Api where
  module := "mlkem16"
  name := "vg_mlkem16_cbd2"
  sig := cbd2_16Sig
  writeArgs := true
  contracts := some fun A stack => cbd2_16Contract A stack
  summary := "`SamplePolyCBD₂` (FIPS 203 Algorithm 8 with `η` = 2): writes the polynomial \
    sampled from the 128 bytes `*b` to `*f` (256 coefficients less than `q` = 3329)." ++
    ctDoc "cbd2_16Contract"
  safety := []

/-- `vg_mlkem*_kpke_keygen` of the parameter set `p` on every target, with
`kpkeKeyGenContract p.k`. -/
def Params.kpkeKeyGenApi (p : Params) : Api where
  module := p.module
  name := p.fn "kpke_keygen"
  sig := kpkeKeyGenSig p.k
  writeArgs := true
  contracts := some fun A stack => kpkeKeyGenContract p.k A stack
  summary := s!"{p.name} K-PKE key generation after sampling (FIPS 203 Algorithm 13, lines \
    16–20). The inputs are the matrix `Â` in `*a` ({p.k * p.k} polynomials, by rows) and the \
    vectors `s` and `e` in `*se` ({p.k} polynomials each, one after the other), each \
    polynomial 256 `u16` coefficients reduced modulo `q` = 3329. Writes `ByteEncode₁₂(t̂)` to \
    `*ek` and `ByteEncode₁₂(ŝ)` to `*dk`, with `ŝ = NTT(s)` and `t̂ = Â ∘ ŝ + NTT(e)`.\n\n\
    Contract: `VG.Spec.MlKem.kpkeKeyGenContract`. Constant time: only the pointers may affect \
    timing."
  safety := [reduced16Safety "a" (p.k * p.k), reduced16Safety "se" (2 * p.k), noiseSafety "se",
    mulScratchDoc]

/-- `vg_mlkem*_kpke_encrypt` of the parameter set `p` on every target, with
`p.kpkeEncryptContract`. -/
def Params.kpkeEncryptApi (p : Params) : Api where
  module := p.module
  name := p.fn "kpke_encrypt"
  sig := p.kpkeEncryptSig
  writeArgs := true
  contracts := some fun A stack => p.kpkeEncryptContract A stack
  summary := s!"{p.name} K-PKE encryption after sampling (FIPS 203 Algorithm 14, lines 2 and 18–23). \
    The inputs are:\n\
    * the matrix `Â` in `*a` ({p.k * p.k} polynomials, by rows);\n\
    * the encoded `t̂` in `*t` (the first {384 * p.k} bytes of the encryption key);\n\
    * the vectors `y` and `e₁` ({p.k} polynomials each) and the polynomial `e₂` in `*r`, one \
    after the other;\n\
    * the message in `*m`.\n\n\
    Each polynomial is 256 `u16` coefficients reduced modulo `q` = 3329. Writes the \
    ciphertext to `*ct`.\n\n\
    Contract: `VG.Spec.MlKem.Params.kpkeEncryptContract`. Constant time: only the pointers \
    may affect timing."
  safety := [reduced16Safety "a" (p.k * p.k), reduced16Safety "r" (2 * p.k + 1),
    noiseSafety "r", mulScratchDoc]

/-- `vg_mlkem*_kpke_decrypt` of the parameter set `p` on every target, with
`p.kpkeDecryptContract`. -/
def Params.kpkeDecryptApi (p : Params) : Api where
  module := p.module
  name := p.fn "kpke_decrypt"
  sig := p.kpkeDecryptSig
  writeArgs := true
  contracts := some fun A stack => p.kpkeDecryptContract A stack
  summary := s!"{p.name} K-PKE decryption (FIPS 203 Algorithm 15): writes the message that \
    the ciphertext `*ct` decrypts to with the decryption key `*s` ({384 * p.k} bytes) to \
    `*m`.\n\n\
    Contract: `VG.Spec.MlKem.Params.kpkeDecryptContract`. Constant time: only the pointers \
    may affect timing."
  safety := [mulScratchDoc]

/-- `vg_mlkem768_kpke_keygen` on every target. -/
def kpkeKeyGenApi : Api := mlKem768.kpkeKeyGenApi
/-- `vg_mlkem768_kpke_encrypt` on every target. -/
def kpkeEncryptApi : Api := mlKem768.kpkeEncryptApi
/-- `vg_mlkem768_kpke_decrypt` on every target. -/
def kpkeDecryptApi : Api := mlKem768.kpkeDecryptApi

end VG.Spec.MlKem

namespace VG.Spec.MlKem1024

open VG.Spec.MlKem

/-- `vg_mlkem1024_kpke_keygen` on every target. -/
def kpkeKeyGenApi : Api := mlKem1024.kpkeKeyGenApi
/-- `vg_mlkem1024_kpke_encrypt` on every target. -/
def kpkeEncryptApi : Api := mlKem1024.kpkeEncryptApi
/-- `vg_mlkem1024_kpke_decrypt` on every target. -/
def kpkeDecryptApi : Api := mlKem1024.kpkeDecryptApi

end VG.Spec.MlKem1024
