module

public import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ML-DSA: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/MlDsa/Contract.lean` and
`Spec/MlDsa/CachedVerify.lean`, are trusted.

The functions on polynomials that ML-DSA's key generation, signing and
verification are composed of, each one step of FIPS 204, in terms of
`Spec/MlDsa.lean`, for any target: `A` is the target's calling convention.
They serve every parameter set, which some take as public arguments.

A polynomial of `R_q` or `T_q` is stored as `[u32; 256]`, coefficient `i`
as the native (little-endian) `u32` at byte `4i`, which is less than `q`
(`Reduced`): the integer that represents it (`polyAt`). A polynomial of `R`
with coefficients of absolute value less than `q/2` (such as `s₁`, `y` or
`t₀`) is stored as the polynomial of `R_q` it casts to (`toRq`), from which
`mod± q` recovers it. A polynomial with coefficients in `ℕ` (`t₁`, `w₁`) is
stored as its coefficients (`natPolyAt`), and a hint polynomial of `R_2` as
coefficients 0 and 1 (`hintAt`: a coefficient is 1 if it is not 0).

Everything is secret, and the functions are constant time, but for
those that sample by rejection or decode a hint, which may leak what their
contracts say: `vg_mldsa_rej_ntt_poly` its seed (public in ML-DSA: `ρ` and
two indices), `vg_mldsa_rej_bounded_poly` which half-bytes of its XOF output
it rejects, `vg_mldsa_sample_in_ball` its seed `c̃`, and
`vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack` the hint. Functions
with working space `scratch` may leave intermediate values in it. The
functions may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), and take the number of bytes of stack
below the stack pointer that their calls and frames use (`stack`, see
`Sig.contract`), which depends on the target.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

open VG.Spec.Sha3 (bytesAt)

/-! ## Polynomials in memory -/

/-- The `u32` coefficient `i` of the polynomial stored at `p`. -/
def coeffAt (m : Mem) (p : Addr) (i : Nat) : BitVec 32 := m.readW (p + BitVec.ofNat 64 (4 * i)) 32

/-- The polynomial of `R_q` stored as `[u32; 256]` at `p`: coefficient `i` is
the `u32` at `p + 4i`, modulo `q`. -/
def polyAt (m : Mem) (p : Addr) : Poly := Vector.ofFn fun i => Fin.ofNat q (coeffAt m p i.val).toNat

/-- The polynomial at `p` is stored reduced: each coefficient is less than
`q`, so it is the integer that represents its element of `ℤ_q`. -/
def Reduced (m : Mem) (p : Addr) : Prop := ∀ i < n, (coeffAt m p i).toNat < q

/-- `f` is stored at `p`, reduced. -/
def PolyIs (m : Mem) (p : Addr) (f : Poly) : Prop := Reduced m p ∧ polyAt m p = f

/-- The polynomial with coefficients in `ℕ` stored as `[u32; 256]` at `p`. -/
def natPolyAt (m : Mem) (p : Addr) : Vector Nat n := Vector.ofFn fun i => (coeffAt m p i.val).toNat

/-- `f` is stored at `p`, as its coefficients. -/
def NatPolyIs (m : Mem) (p : Addr) (f : Vector Nat n) : Prop := natPolyAt m p = f

/-- The hint of `R_2^k` stored as `k` polynomials `[u32; 256]` at `p`:
coefficient `j` of polynomial `i` is 1 if the `u32` at `p + 1024i + 4j` is
not 0. -/
def hintAt (m : Mem) (p : Addr) (k : Nat) : List (Vector Bool n) :=
  (List.range k).map fun i => Vector.ofFn fun j => coeffAt m p (256 * i + j.val) ≠ 0

/-- `h` is stored at `p` as `k` polynomials of coefficients 0 and 1. -/
def HintIs (m : Mem) (p : Addr) (k : Nat) (h : List (Vector Bool n)) : Prop :=
  h.length = k ∧ ∀ i < k, ∀ j < n, coeffAt m p (256 * i + j) = (h.getD i (Vector.replicate n false))[j]!.toNat

/-- The number of 1s in a hint. -/
def hintOnes (h : List (Vector Bool n)) : Nat := (h.map fun hi => (hi.toList.filter id).length).sum

/-! ## Arithmetic -/

/-- `f: *mut [u32; 256], scratch: *mut [u64; 128]`: a polynomial transformed in
place. -/
def inPlaceSig : Sig where
  params := [("f", .array true .u32 256), ("scratch", .array true .u64 128)]

/-- If the polynomial at `f` is reduced, it becomes `t` of it, reduced. -/
def inPlaceContract {M : ISA} (A : Abi M) (t : Poly → Poly) (stack : Nat := 0) : Contract M :=
  inPlaceSig.contract A
    (pre := fun f _scratch m => Reduced m f)
    (post := fun f _scratch m m' _ => PolyIs m' f (t (polyAt m f)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_ntt`: `NTT` (Algorithm 41) in place. -/
def nttContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A ntt stack

/-- `vg_mldsa_inv_ntt`: `NTT⁻¹` (Algorithm 42) in place. -/
def nttInvContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A nttInv stack

/-- `h: *mut [u32; 256], f: *const [u32; 256], g: *const [u32; 256]`. -/
def mulSig : Sig where
  params := [("h", .array true .u32 256), ("f", .array false .u32 256),
    ("g", .array false .u32 256)]

/-- `vg_mldsa_multiply_ntt`: if the polynomials at `f` and `g` are reduced,
writes `MultiplyNTT(f, g)` (Algorithm 45) to `h`, reduced. -/
def mulContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun _h f g m => Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ => PolyIs m' h (multiplyNTT (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_multiply_add_ntt`: if the polynomials at `h`, `f` and `g` are
reduced, `h` becomes `AddNTT(h, MultiplyNTT(f, g))` (Algorithms 44 and 45,
line 4 of Algorithm 48), reduced. -/
def mulAddContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun h f g m => Reduced m h ∧ Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ =>
      PolyIs m' h (add (polyAt m h) (multiplyNTT (polyAt m f) (polyAt m g))))
    (writeArgs := true)
    (stack := stack)

/-- `f: *mut [u32; 256], g: *const [u32; 256]`. -/
def accSig : Sig where
  params := [("f", .array true .u32 256), ("g", .array false .u32 256)]

/-- `vg_mldsa_add`: if the polynomials at `f` and `g` are reduced, `f`
becomes `f + g` (Algorithm 44), reduced. -/
def addContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  accSig.contract A
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (add (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_sub`: if the polynomials at `f` and `g` are reduced, `f`
becomes `f - g`, reduced. -/
def subContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  accSig.contract A
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (sub (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := stack)

/-! ## Sampling -/

/-- `vg_mldsa_rej_ntt_poly(seed: *const [u8; 34], a: *mut [u32; 256], scratch: *mut [u64; 256]) -> u32`. -/
def rejNTTSig : Sig where
  params := [("seed", .array false .u8 34), ("a", .array true .u32 256),
    ("scratch", .array true .u64 256)]
  ret := some .u32

/-- With the 34 bytes `ρ` at `seed`: writes `RejNTTPoly(ρ)` (Algorithm 30) to
`a`, reduced, and returns 1; or returns 0 (see `Outcome`), and `a` is
unspecified. May leak `ρ`. -/
def rejNTTContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  rejNTTSig.contract A
    (post := fun seed a _scratch m m' r =>
      (r = 1 → Reduced m' a) ∧
        Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt m seed 34)) r (polyAt m' a))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _a _scratch m => leakBytes (bytesAt m seed 34))

/-- `vg_mldsa_rej_ntt_poly4(seeds: *const [u8; 136], a: *mut [u32; 1024], scratch: *mut [u64; 1024]) -> u32`. -/
def rejNTT4Sig : Sig where
  params := [("seeds", .array false .u8 136), ("a", .array true .u32 1024),
    ("scratch", .array true .u64 1024)]
  ret := some .u32

/-- Seed `k` of four at `seeds`: the 34 bytes from byte `34 k`. -/
def seed4 (m : Mem) (seeds : Addr) (k : Nat) : List Byte := bytesAt m (seeds + BitVec.ofNat 64 (34 * k)) 34

/-- Polynomial `k` of four at `a`: from byte `1024 k`. -/
def poly4 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (1024 * k)

/-- `RejNTTPoly` four times: with the four 34-byte seeds `ρ₀, …, ρ₃` at
`seeds` (`seed4`), writes `RejNTTPoly(ρₖ)` (Algorithm 30) to the polynomial
at `a + 1024 k` (`poly4`), reduced, for each `k`, and returns 1; or returns
0 if the loop of `RejNTTPoly` does not finish within the least bound
Appendix C allows (`minBounds`) for one of them, and `a` is unspecified.
May leak the seeds. -/
def rejNTT4Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  rejNTT4Sig.contract A
    (post := fun seeds a _scratch m m' r =>
      (r = 1 → ∀ k < 4, Reduced m' (poly4 a k)) ∧
        ((r = 1 ∧ ∀ k < 4, ∃ b : Bounds, rejNTTPoly b.rejNTT (seed4 m seeds k) = some (polyAt m' (poly4 a k))) ∨
          (r = 0 ∧ ∃ k < 4, rejNTTPoly minBounds.rejNTT (seed4 m seeds k) = none)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seeds _a _scratch m => leakBytes (bytesAt m seeds 136))

/-- `vg_mldsa_rej_bounded_poly(seed: *const [u8; 66], eta: u32, a: *mut [u32; 256], scratch: *mut [u64; 256]) -> u32`. -/
def rejBoundedSig : Sig where
  params := [("seed", .array false .u8 66), ("eta", .int .u32 true), ("a", .array true .u32 256),
    ("scratch", .array true .u64 256)]
  ret := some .u32

/-- If `η` = `eta` is 2 or 4: with the 66 bytes `ρ` at `seed`, writes
`RejBoundedPoly(ρ)` (Algorithm 31) to `a` (as a polynomial of `R_q`),
reduced, and returns 1; or returns 0 (see `Outcome`), and `a` is
unspecified. May leak which half-bytes it rejects (`rejBoundedLeak`). -/
def rejBoundedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  rejBoundedSig.contract A
    (pre := fun _seed eta _a _scratch _m => eta.toNat = 2 ∨ eta.toNat = 4)
    (post := fun seed eta a _scratch m m' r =>
      (r = 1 → Reduced m' a) ∧
        Outcome (fun b => (rejBoundedPoly eta.toNat b.rejBounded (bytesAt m seed 66)).map toRq) r
          (polyAt m' a))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed eta _a _scratch m => rejBoundedLeak eta.toNat (bytesAt m seed 66))

/-- `vg_mldsa_expand_mask_poly(seed: *const [u8; 66], gamma1: u32, a: *mut [u32; 256], scratch: *mut [u64; 256])`. -/
def expandMaskSig : Sig where
  params := [("seed", .array false .u8 66), ("gamma1", .int .u32 true),
    ("a", .array true .u32 256), ("scratch", .array true .u64 256)]

/-- If `γ₁` = `gamma1` is `2¹⁷` or `2¹⁹`: with the 66 bytes `ρ′` at `seed`,
writes `BitUnpack(H(ρ′, 32c), γ₁ - 1, γ₁)` for `c = 1 + bitlen (γ₁ - 1)` to
`a` (as a polynomial of `R_q`), reduced: a polynomial of `ExpandMask`
(Algorithm 34, lines 4 and 5, with `ρ′ = ρ ‖ IntegerToBytes(μ + r, 2)`). -/
def expandMaskContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandMaskSig.contract A
    (pre := fun _seed gamma1 _a _scratch _m => gamma1.toNat = 2 ^ 17 ∨ gamma1.toNat = 2 ^ 19)
    (post := fun seed gamma1 a _scratch m m' _ =>
      PolyIs m' a (toRq (bitUnpack (H (bytesAt m seed 66) (32 * (1 + bitlen (gamma1.toNat - 1))))
        (gamma1.toNat - 1) gamma1.toNat)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_expand_mask_poly4(seeds: *const [u8; 264], gamma1: u32, a: *mut [u32; 1024], scratch: *mut [u64; 1024])`. -/
def expandMask4Sig : Sig where
  params := [("seeds", .array false .u8 264), ("gamma1", .int .u32 true),
    ("a", .array true .u32 1024), ("scratch", .array true .u64 1024)]

/-- Seed `k` of four at `seeds`: the 66 bytes from byte `66 k`. -/
def seed66 (m : Mem) (seeds : Addr) (k : Nat) : List Byte := bytesAt m (seeds + BitVec.ofNat 64 (66 * k)) 66

/-- Four polynomials of `ExpandMask`: if `γ₁` = `gamma1` is `2¹⁷` or `2¹⁹`,
with the four 66-byte seeds `ρ′₀, …, ρ′₃` at `seeds` (`seed66`), writes
`BitUnpack(H(ρ′ₖ, 32c), γ₁ - 1, γ₁)` for `c = 1 + bitlen (γ₁ - 1)` to the
polynomial at `a + 1024 k` (`poly4`, as a polynomial of `R_q`), reduced,
for each `k`: what `expandMaskContract` says of each. -/
def expandMask4Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandMask4Sig.contract A
    (pre := fun _seeds gamma1 _a _scratch _m => gamma1.toNat = 2 ^ 17 ∨ gamma1.toNat = 2 ^ 19)
    (post := fun seeds gamma1 a _scratch m m' _ => ∀ k < 4,
      PolyIs m' (poly4 a k) (toRq (bitUnpack (H (seed66 m seeds k) (32 * (1 + bitlen (gamma1.toNat - 1))))
        (gamma1.toNat - 1) gamma1.toNat)))
    (writeArgs := true)
    (stack := stack)

/-- The values of `(λ/4, τ)` of the parameter sets (Table 1). -/
def ballParams : List (Nat × Nat) := [(32, 39), (48, 49), (64, 60)]

/-- `vg_mldsa_sample_in_ball(ctilde: *const u8, len: usize, tau: u32, c: *mut [u32; 256], scratch: *mut [u64; 256]) -> u32`. -/
def sampleInBallSig : Sig where
  params := [("ctilde", .slice false .u8 "len"), ("tau", .int .u32 true),
    ("c", .array true .u32 256), ("scratch", .array true .u64 256)]
  ret := some .u32

/-- If `(len, τ)` = `(len, tau)` is in `ballParams`: with the `len` bytes `ρ`
at `ctilde`, writes `SampleInBall(ρ)` (Algorithm 29) to `c` (as a polynomial
of `R_q`), reduced, and returns 1; or returns 0 (see `Outcome`), and `c` is
unspecified. May leak `ρ`. -/
def sampleInBallContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sampleInBallSig.contract A
    (pre := fun _ctilde len tau _c _scratch _m => (len.toNat, tau.toNat) ∈ ballParams)
    (post := fun ctilde len tau c _scratch m m' r =>
      (r = 1 → Reduced m' c) ∧
        Outcome (fun b => (sampleInBall tau.toNat b.ball (bytesAt m ctilde len.toNat)).map toRq) r
          (polyAt m' c))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctilde len _tau _c _scratch m => leakBytes (bytesAt m ctilde len.toNat))

/-! ## Rounding and hints -/

/-- `vg_mldsa_power2round(t: *const [u32; 256], t1: *mut [u32; 256], t0: *mut [u32; 256])`. -/
def power2RoundSig : Sig where
  params := [("t", .array false .u32 256), ("t1", .array true .u32 256),
    ("t0", .array true .u32 256)]

/-- If the polynomial at `t` is reduced: writes the `r₁` of
`Power2Round(tᵢ)` (Algorithm 35) of its coefficients to `t1`, and their
`r₀` to `t0` (as a polynomial of `R_q`), reduced. -/
def power2RoundContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  power2RoundSig.contract A
    (pre := fun t _t1 _t0 m => Reduced m t)
    (post := fun t t1 t0 m m' _ =>
      NatPolyIs m' t1 ((polyAt m t).map fun c => (power2Round c).1.toNat) ∧
        PolyIs m' t0 ((polyAt m t).map fun c => ofInt (power2Round c).2))
    (writeArgs := true)
    (stack := stack)

/-- The values of `γ₂` of the parameter sets (Table 1). -/
def gamma2s : List Nat := [(q - 1) / 88, (q - 1) / 32]

/-- `r: *const [u32; 256], gamma2: u32, out: *mut [u32; 256]`. -/
def bitsSig : Sig where
  params := [("r", .array false .u32 256), ("gamma2", .int .u32 true),
    ("out", .array true .u32 256)]

/-- `vg_mldsa_high_bits`: if `γ₂` = `gamma2` is in `gamma2s` and the
polynomial at `r` is reduced, writes the `HighBits(rᵢ)` (Algorithm 37) of
its coefficients to `out`. -/
def highBitsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitsSig.contract A
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ =>
      NatPolyIs m' out ((polyAt m r).map fun c => (highBits gamma2.toNat c).toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_low_bits`: if `γ₂` = `gamma2` is in `gamma2s` and the
polynomial at `r` is reduced, writes the `LowBits(rᵢ)` (Algorithm 38) of its
coefficients to `out` (as a polynomial of `R_q`), reduced. -/
def lowBitsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitsSig.contract A
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ =>
      PolyIs m' out ((polyAt m r).map fun c => ofInt (lowBits gamma2.toNat c)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_norm_lt(f: *const [u32; 256], bound: u32) -> u32`. -/
def normLtSig : Sig where
  params := [("f", .array false .u32 256), ("bound", .int .u32 true)]
  ret := some .u32

/-- If the polynomial at `f` is reduced: returns 1 if `‖f‖∞ < bound` (§2.3),
and 0 otherwise. -/
def normLtContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  normLtSig.contract A
    (pre := fun f _bound m => Reduced m f)
    (post := fun f bound m _m' r => r = if normRq [polyAt m f] < bound.toNat then 1 else 0)
    (stack := stack)

/-- `vg_mldsa_make_hint(z: *const [u32; 256], r: *const [u32; 256], gamma2: u32, h: *mut [u32; 256]) -> u32`. -/
def makeHintSig : Sig where
  params := [("z", .array false .u32 256), ("r", .array false .u32 256),
    ("gamma2", .int .u32 true), ("h", .array true .u32 256)]
  ret := some .u32

/-- If `γ₂` = `gamma2` is in `gamma2s` and the polynomials at `z` and `r` are
reduced: writes the `MakeHint(zᵢ, rᵢ)` (Algorithm 39) of their coefficients
to `h`, as 1 for true and 0 for false, and returns the number of 1s. -/
def makeHintContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  makeHintSig.contract A
    (pre := fun z r gamma2 _h m => gamma2.toNat ∈ gamma2s ∧ Reduced m z ∧ Reduced m r)
    (post := fun z r gamma2 h m m' ret =>
      let hint := Vector.zipWith (makeHint gamma2.toNat) (polyAt m z) (polyAt m r)
      HintIs m' h 1 [hint] ∧ ret.toNat = hintOnes [hint])
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_use_hint(h: *const [u32; 256], r: *const [u32; 256], gamma2: u32, out: *mut [u32; 256])`. -/
def useHintSig : Sig where
  params := [("h", .array false .u32 256), ("r", .array false .u32 256),
    ("gamma2", .int .u32 true), ("out", .array true .u32 256)]

/-- If `γ₂` = `gamma2` is in `gamma2s` and the polynomial at `r` is reduced:
writes the `UseHint(hᵢ, rᵢ)` (Algorithm 40) of the coefficients of the hint
polynomial at `h` and of `r` to `out`. -/
def useHintContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  useHintSig.contract A
    (pre := fun _h r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun h r gamma2 out m m' _ =>
      NatPolyIs m' out (Vector.zipWith (fun hj rj => (useHint gamma2.toNat hj rj).toNat)
        ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m r)))
    (writeArgs := true)
    (stack := stack)

/-! ## Encodings -/

/-- The bounds `b` that `SimpleBitPack` packs to: `2^(bitlen (q - 1) - d) - 1`
for `t₁` (Algorithm 22) and `(q - 1)/(2γ₂) - 1` for `w₁` (Algorithm 28). -/
def simpleBitPackBounds : List Nat := [t1Max, 43, 15]

/-- `vg_mldsa_simple_bit_pack(f: *const [u32; 256], b: u32, out: *mut u8, len: usize)`. -/
def simpleBitPackSig : Sig where
  params := [("f", .array false .u32 256), ("b", .int .u32 true), ("out", .slice true .u8 "len")]

/-- If `b` is in `simpleBitPackBounds`, `len = 32 · bitlen b` and each
coefficient of the polynomial at `f` is at most `b`: writes
`SimpleBitPack(f, b)` (Algorithm 16) to `out`. -/
def simpleBitPackContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  simpleBitPackSig.contract A
    (pre := fun f b _out len m =>
      b.toNat ∈ simpleBitPackBounds ∧ len.toNat = 32 * bitlen b.toNat ∧
        ∀ i < n, (coeffAt m f i).toNat ≤ b.toNat)
    (post := fun f b out len m m' _ =>
      bytesAt m' out len.toNat = simpleBitPack (natPolyAt m f) b.toNat)
    (writeArgs := true)
    (stack := stack)

/-- The `(a, b)` that `BitPack` and `BitUnpack` pack to and from: `(η, η)` for
`s₁` and `s₂` (Algorithm 24), `(2^(d-1) - 1, 2^(d-1))` for `t₀`, and
`(γ₁ - 1, γ₁)` for `z` (Algorithm 26). -/
def bitPackParams : List (Nat × Nat) :=
  [(2, 2), (4, 4), (2 ^ (d - 1) - 1, 2 ^ (d - 1)), (2 ^ 17 - 1, 2 ^ 17), (2 ^ 19 - 1, 2 ^ 19)]

/-- `vg_mldsa_bit_pack(f: *const [u32; 256], a: u32, b: u32, out: *mut u8, len: usize)`. -/
def bitPackSig : Sig where
  params := [("f", .array false .u32 256), ("a", .int .u32 true), ("b", .int .u32 true),
    ("out", .slice true .u8 "len")]

/-- If `(a, b)` is in `bitPackParams`, `len = 32 · bitlen (a + b)`, and the
polynomial at `f` is reduced with each coefficient `fᵢ mod± q` in
`[-a, b]`: writes `BitPack(f mod± q, a, b)` (Algorithm 17) to `out`. -/
def bitPackContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitPackSig.contract A
    (pre := fun f a b _out len m =>
      (a.toNat, b.toNat) ∈ bitPackParams ∧ len.toNat = 32 * bitlen (a.toNat + b.toNat) ∧
        Reduced m f ∧ ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt m f i).toNat q ∧
          modPm (coeffAt m f i).toNat q ≤ b.toNat)
    (post := fun f a b out len m m' _ =>
      bytesAt m' out len.toNat = bitPack ((polyAt m f).map fun c => modPm c.val q) a.toNat b.toNat)
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_bit_unpack(v: *const u8, len: usize, a: u32, b: u32, f: *mut [u32; 256])`. -/
def bitUnpackSig : Sig where
  params := [("v", .slice false .u8 "len"), ("a", .int .u32 true), ("b", .int .u32 true),
    ("f", .array true .u32 256)]

/-- If `(a, b)` is in `bitPackParams` and `len = 32 · bitlen (a + b)`: writes
`BitUnpack(v, a, b)` (Algorithm 19) of the `len` bytes `v` at `v` to `f` (as
a polynomial of `R_q`), reduced. -/
def bitUnpackContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitUnpackSig.contract A
    (pre := fun _v len a b _f _m =>
      (a.toNat, b.toNat) ∈ bitPackParams ∧ len.toNat = 32 * bitlen (a.toNat + b.toNat))
    (post := fun v len a b f m m' _ =>
      PolyIs m' f (toRq (bitUnpack (bytesAt m v len.toNat) a.toNat b.toNat)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mldsa_unpack_t1(v: *const [u8; 320], f: *mut [u32; 256])`. -/
def unpackT1Sig : Sig where
  params := [("v", .array false .u8 320), ("f", .array true .u32 256)]

/-- Writes `t₁ · 2ᵈ` for `t₁ = SimpleBitUnpack(v, 2^(bitlen (q - 1) - d) - 1)`
(Algorithm 18, line 3 of Algorithm 23) of the 320 bytes at `v` to `f` (as a
polynomial of `R_q`), reduced: the `t₁ · 2ᵈ` of line 9 of Algorithm 8. -/
def unpackT1Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  unpackT1Sig.contract A
    (post := fun v f m m' _ =>
      PolyIs m' f ((simpleBitUnpack (bytesAt m v 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)))
    (writeArgs := true)
    (stack := stack)

/-- The values of `(ω, k)` of the parameter sets (Table 1). -/
def hintParams : List (Nat × Nat) := [(80, 4), (55, 6), (75, 8)]

/-- `vg_mldsa_hint_bit_pack(h: *const u32, hlen: usize, omega: u32, y: *mut u8, len: usize)`. -/
def hintBitPackSig : Sig where
  params := [("h", .slice false .u32 "hlen"), ("omega", .int .u32 true),
    ("y", .slice true .u8 "len")]

/-- If `(ω, k)` = `(omega, len - omega)` is in `hintParams`, `hlen = 256k`,
and the hint of `k` polynomials at `h` has at most `ω` 1s: writes
`HintBitPack(h)` (Algorithm 20) to `y`. May leak the hint. -/
def hintBitPackContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  hintBitPackSig.contract A
    (pre := fun h hlen omega _y len m =>
      (omega.toNat, len.toNat - omega.toNat) ∈ hintParams ∧ omega.toNat ≤ len.toNat ∧
        hlen.toNat = 256 * (len.toNat - omega.toNat) ∧
        hintOnes (hintAt m h (len.toNat - omega.toNat)) ≤ omega.toNat)
    (post := fun h _hlen omega y len m m' _ =>
      bytesAt m' y len.toNat =
        hintBitPack omega.toNat (len.toNat - omega.toNat) (hintAt m h (len.toNat - omega.toNat)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun h hlen _omega _y _len m =>
      (List.range hlen.toNat).map fun i => (coeffAt m h i).toNat)

/-- `vg_mldsa_hint_bit_unpack(y: *const u8, len: usize, omega: u32, h: *mut u32, hlen: usize) -> u32`. -/
def hintBitUnpackSig : Sig where
  params := [("y", .slice false .u8 "len"), ("omega", .int .u32 true),
    ("h", .slice true .u32 "hlen")]
  ret := some .u32

/-- If `(ω, k)` = `(omega, len - omega)` is in `hintParams` and `hlen = 256k`:
if `HintBitUnpack(y)` (Algorithm 21) of the `len` bytes `y` at `y` is a hint,
writes it to `h` as `k` polynomials of coefficients 0 and 1 and returns 1;
if it is `⊥`, returns 0, and `h` is unspecified. May leak `y`. -/
def hintBitUnpackContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  hintBitUnpackSig.contract A
    (pre := fun _y len omega _h hlen _m =>
      (omega.toNat, len.toNat - omega.toNat) ∈ hintParams ∧ omega.toNat ≤ len.toNat ∧
        hlen.toNat = 256 * (len.toNat - omega.toNat))
    (post := fun y len omega h _hlen m m' r =>
      match hintBitUnpack omega.toNat (len.toNat - omega.toNat) (bytesAt m y len.toNat) with
      | some hint => r = 1 ∧ HintIs m' h (len.toNat - omega.toNat) hint
      | none => r = 0)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun y len _omega _h _hlen m => leakBytes (bytesAt m y len.toNat))

end VG.Proof.MlDsa
