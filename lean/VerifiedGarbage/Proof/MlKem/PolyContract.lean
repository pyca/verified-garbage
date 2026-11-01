module

public import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM: the contracts of the polynomial primitives, on every target

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The contracts of the functions that ML-KEM's key generation, encapsulation
and decapsulation (`Spec/MlKem/Contract.lean`) are composed of, each one
step of FIPS 203 on polynomials, in terms of `Spec/MlKem.lean`, for any
target: `A` is the target's calling convention. They do not depend on the
parameter set, so they are named `vg_mlkem_*`.

A polynomial (an element of `ℤ_q²⁵⁶`, of `R_q` or `T_q`) is stored as
`[u32; 256]`, coefficient `i` as the native (little-endian) `u32` at byte
`4i`, which is less than `q` (`Reduced`): the integer that represents it
(`polyAt`). Every function takes its polynomials reduced and leaves them
reduced.

Everything is secret, and the functions are constant time, but for
`vg_mlkem_sample_ntt`, whose seed is public in ML-KEM (it is `ρ` and two
indices) and which may leak it: its loop takes a number of iterations that
depends on it. Functions with working space `scratch` may leave
intermediate values in it, which the caller must destroy (FIPS 203 §3.3).
The functions may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`), and take the number of bytes of
stack below the stack pointer that their calls and frames use (`stack`, see
`Sig.contract`), which depends on the target.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec VG.Spec.MlKem
open Sha3 (bytesAt)

/-- The `u32` coefficient `i` of the polynomial stored at `p`. -/
def coeffAt (m : Mem) (p : Addr) (i : Nat) : BitVec 32 := m.readW (p + BitVec.ofNat 64 (4 * i)) 32

/-- The polynomial stored as `[u32; 256]` at `p`: coefficient `i` is the
`u32` at `p + 4i`, modulo `q`. -/
def polyAt (m : Mem) (p : Addr) : Poly := Vector.ofFn fun i => ofNat (coeffAt m p i.val).toNat

/-- The polynomial at `p` is stored reduced: each coefficient is less than
`q`, so it is the integer that represents its element of `ℤ_q`. -/
def Reduced (m : Mem) (p : Addr) : Prop := ∀ i < n, (coeffAt m p i).toNat < q

/-- `f` is stored at `p`, reduced. -/
def PolyIs (m : Mem) (p : Addr) (f : Poly) : Prop := Reduced m p ∧ polyAt m p = f

/-- `f: *mut [u32; 256], scratch: *mut [u64; 128]`: a polynomial transformed in
place. -/
def inPlaceSig (name : String) : Sig where
  params := [(name, .array true .u32 256), ("scratch", .array true .u64 128)]

/-- If the polynomial at `f` is reduced, it becomes `t` of it, reduced. -/
def inPlaceContract {M : ISA} (A : Abi M) (t : Poly → Poly) (stack : Nat := 0) : Contract M :=
  (inPlaceSig "f").contract A
    (pre := fun f _scratch m => Reduced m f)
    (post := fun f _scratch m m' _ => PolyIs m' f (t (polyAt m f)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_ntt(f: *mut [u32; 256], scratch: *mut [u64; 128])`: `NTT`
(Algorithm 9) in place. -/
def nttContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A ntt stack

/-- `vg_mlkem_inv_ntt(f: *mut [u32; 256], scratch: *mut [u64; 128])`: `NTT⁻¹`
(Algorithm 10) in place. -/
def nttInvContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A nttInv stack

/-- `h: *mut [u32; 256], f: *const [u32; 256], g: *const [u32; 256], scratch: *mut [u64; 128]`. -/
def mulSig : Sig where
  params := [("h", .array true .u32 256), ("f", .array false .u32 256),
    ("g", .array false .u32 256), ("scratch", .array true .u64 128)]

/-- `vg_mlkem_multiply_ntts`: if the polynomials at `f` and `g` are reduced,
writes `MultiplyNTTs(f, g)` (Algorithm 11) to `h`, reduced. -/
def mulContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun _h f g _scratch m => Reduced m f ∧ Reduced m g)
    (post := fun h f g _scratch m m' _ => PolyIs m' h (multiplyNTTs (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- `f: *mut [u32; 256], g: *const [u32; 256]`. -/
def accSig : Sig where
  params := [("f", .array true .u32 256), ("g", .array false .u32 256)]

/-- `vg_mlkem_add`: if the polynomials at `f` and `g` are reduced, `f`
becomes `f + g` (2.3), reduced. -/
def addContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  accSig.contract A
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (add (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_sub`: if the polynomials at `f` and `g` are reduced, `f`
becomes `f - g`, reduced. -/
def subContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  accSig.contract A
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (sub (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_sample_ntt(seed: *const [u8; 34], a: *mut [u32; 256], scratch: *mut [u64; 256]) -> u32`. -/
def sampleNTTSig : Sig where
  params := [("seed", .array false .u8 34), ("a", .array true .u32 256),
    ("scratch", .array true .u64 256)]
  ret := some .u32

/-- With the 34 bytes `B` at `seed`: writes `SampleNTT(B)` (Algorithm 7) to
`a`, reduced, and returns 1; or returns 0 (see `Outcome`), and `a` is
unspecified. May leak `B`. -/
def sampleNTTContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sampleNTTSig.contract A
    (post := fun seed a _scratch m m' r =>
      (r = 1 → Reduced m' a) ∧
        Outcome (fun iters => sampleNTT iters (bytesAt m seed 34)) r (polyAt m' a))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _a _scratch m => (bytesAt m seed 34).map (·.toNat))

/-- `vg_mlkem_sample_ntt4(seeds: *const [u8; 136], a: *mut [u32; 1024], scratch: *mut [u64; 1024]) -> u32`. -/
def sampleNTT4Sig : Sig where
  params := [("seeds", .array false .u8 136), ("a", .array true .u32 1024),
    ("scratch", .array true .u64 1024)]
  ret := some .u32

/-- Seed `k` of four at `seeds`: the 34 bytes from byte `34 k`. -/
def seed4 (m : Mem) (seeds : Addr) (k : Nat) : List Byte := bytesAt m (seeds + BitVec.ofNat 64 (34 * k)) 34

/-- Polynomial `k` of four at `a`: from byte `1024 k`. -/
def poly4 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (1024 * k)

/-- `SampleNTT` four times: with the four 34-byte seeds `B₀, …, B₃` at
`seeds` (`seed4`), writes `SampleNTT(Bₖ)` (Algorithm 7) to the polynomial at
`a + 1024 k` (`poly4`), reduced, for each `k`, and returns 1; or returns 0
if the loop of `SampleNTT` reaches its bound (`minIterations`) for one of
them, and `a` is unspecified. May leak the seeds. -/
def sampleNTT4Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sampleNTT4Sig.contract A
    (post := fun seeds a _scratch m m' r =>
      (r = 1 → ∀ k < 4, Reduced m' (poly4 a k)) ∧
        ((r = 1 ∧ ∀ k < 4, ∃ iters, sampleNTT iters (seed4 m seeds k) = some (polyAt m' (poly4 a k))) ∨
          (r = 0 ∧ ∃ k < 4, sampleNTT minIterations (seed4 m seeds k) = none)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seeds _a _scratch m => (bytesAt m seeds 136).map (·.toNat))

/-- `vg_mlkem_cbd2(b: *const [u8; 128], f: *mut [u32; 256])`. -/
def cbd2Sig : Sig where
  params := [("b", .array false .u8 128), ("f", .array true .u32 256)]

/-- Writes `SamplePolyCBD₂(B)` (Algorithm 8, `η = 2`) of the 128 bytes `B` at
`b` to `f`, reduced. -/
def cbd2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbd2Sig.contract A
    (post := fun b f m m' _ => PolyIs m' f (samplePolyCBD 2 (bytesAt m b 128)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384])`. -/
def encode12Sig : Sig where
  params := [("f", .array false .u32 256), ("out", .array true .u8 384)]

/-- If the polynomial at `f` is reduced, writes `ByteEncode₁₂` (Algorithm 5)
of it to `out`. -/
def encode12Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encode12Sig.contract A
    (pre := fun f _out m => Reduced m f)
    (post := fun f out m m' _ => bytesAt m' out 384 = encode12 (polyAt m f))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256])`. -/
def decode12Sig : Sig where
  params := [("b", .array false .u8 384), ("f", .array true .u32 256)]

/-- Writes `ByteDecode₁₂` (Algorithm 6, which reduces modulo `q`) of the 384
bytes at `b` to `f`, reduced. -/
def decode12Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decode12Sig.contract A
    (post := fun b f m m' _ => PolyIs m' f (decode12 (bytesAt m b 384)))
    (writeArgs := true)
    (stack := stack)

/-- The values of `d` that ML-KEM-768 compresses to (`d_u`, `d_v` and the 1
of the message, Table 2). -/
def compressWidths : List Nat := [1, 4, 10]

/-- `vg_mlkem_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize)`. -/
def compressEncodeSig : Sig where
  params := [("f", .array false .u32 256), ("d", .int .u32 true), ("out", .slice true .u8 "len")]

/-- If `d` is in `compressWidths`, `len = 32d` and the polynomial at `f` is
reduced: writes `ByteEncode_d(Compress_d(f))` to `out`. -/
def compressEncodeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressEncodeSig.contract A
    (pre := fun f d _out len m =>
      d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat ∧ Reduced m f)
    (post := fun f d out len m m' _ =>
      bytesAt m' out len.toNat = compressEncode d.toNat (polyAt m f))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256])`. -/
def decodeDecompressSig : Sig where
  params := [("b", .slice false .u8 "len"), ("d", .int .u32 true), ("f", .array true .u32 256)]

/-- If `d` is in `compressWidths` and `len = 32d`: writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`,
reduced. -/
def decodeDecompressContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decodeDecompressSig.contract A
    (pre := fun _b len d _f _m => d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat)
    (post := fun b len d f m m' _ =>
      PolyIs m' f (decodeDecompress d.toNat (bytesAt m b len.toNat)))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.MlKem
