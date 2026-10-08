import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace CombDot
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

def product (j : Nat) : List Instr :=
 [.ldrq .v0 .x1 (1024*j),.ldrq .v1 .x2 (1024*j)] ++
 (if j=0 then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
 else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)])
def dot (n : Nat) : Prog isa :=
 .seq (.block (consts ++ [.movz .x .x12 64 0])) <|
 .loop (.block ((List.range n).flatMap product ++
 [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
 .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
 .vop (.perm .uzp2 .s4 .v0 .v2 .v3)] ++ csub .v0 .v4 ++
 [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
 .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12)
def dotAt (n : Nat) (h f g : Ptr) : Prog isa :=
 callAt ("vg_mldsa_dot" ++ toString n) (dot n) [(.x0,.ptr h),(.x1,.ptr f),(.x2,.ptr g)]
end CombDot
open VG VG.AArch64
namespace WindowMask
open VG.Impl.MlDsa.AArch64.Call
-- Fixed-address four-vector mask per iteration. The sampler returns w0 in {0,1}.
def maskN (a : Ptr) (count : Nat) : Prog isa :=
 .seq (.block ([.movz .x .x8 0 0,.sub .w .x8 .x8 .x0,.vop (.dup .s4 .v0 .x8)] ++
  lea .x1 a.1 a.2 ++ [.movz .x .x2 (BitVec.ofNat 16 (count/16)) 0])) <|
 .loop (.block ((List.range 4).flatMap (fun i =>
  [.ldrq .v1 .x1 (16*i),.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x1 (16*i)]) ++
  [.addImm .x .x1 .x1 64,.subImm .x .x2 .x2 1])) (.nonzero .x .x2)
def mask4 (a : Ptr) : Prog isa := maskN a 1024
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
 .seq call (.seq (.block and24) (maskN a 256))
end WindowMask


/-!
# ML-DSA on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

`keyGen P p (seed = x0, pk = x1, sk = x2, scratch = x3) -> w0`:
`ML-DSA.KeyGen_internal(ξ)` (FIPS 204 Algorithm 6) of the parameter set
`p`, with `ξ` at `seed`, as calls of the primitives `P` and of the SHA-3
sponge functions (`Frag.lean`). It keeps `seed` in `x25`, `pk` in `x26`,
`sk` in `x27` and `scratch` in `x28`, and the AND of the results of the
samplers in `x24`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200, the saved registers at 840; `k` and `ℓ`
at 896 (`oKL`); `(ρ, ρ′, K)` at 1024 (`oHX`, 128 bytes); the seed of
`RejNTTPoly` at 1152 (`oSA`, 34 bytes) and of `RejBoundedPoly` at 1216
(`oSB`, 66 bytes); the working space of the primitives at 2048 (2048 bytes);
and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is polynomial
`rℓ + s`, `s₁[j]` (then `ŝ₁[j]`) polynomial `kℓ + j`, `s₂[i]` polynomial
`kℓ + ℓ + i`, and `t`, `t₁` and `t₀` the three after them.

1. `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, and `ρ` and `ρ′` to the seeds.
2. `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` and `s₁ ‖ s₂ = RejBoundedPoly(ρ′ ‖ r ‖ 0)`
   (`ExpandA`, `ExpandS`). After each, `x24 ← x24 ∧ result`, and the
   polynomial is ANDed with `-result` (`mask`): it is zero if the sampler
   failed, so that every polynomial is reduced, and small, whatever the
   samplers return, without a branch.
3. `ρ` and `K` to `sk`; `s₁` and `s₂`, `BitPack`ed, to `sk`; `ŝ₁ = NTT(s₁)`.
4. For each row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, `Power2Round`, and
   `t₁` `SimpleBitPack`ed to `pk`, `t₀` `BitPack`ed to `sk`; `ρ` to `pk`.
5. `tr = H(pk, 64)` to `sk`; return `x24`.

Every address and branch depends only on the pointers, but for what the
samplers leak (`ρ` and which half-bytes `RejBoundedPoly` rejects).
-/

namespace WindowKeygen
open VG.Impl.MlDsa.AArch64.KeyGen

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Spec.MlDsa (Params bitlen)

/-! ## The layout of the working space -/

def oKL : Nat := 896
def oHX : Nat := 1024
def oSA : Nat := 1152
def oSA4 : Nat := 1408
def oSB : Nat := 1216
def oSS : Nat := 2048
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 4096 + 1024 * j

/-- `Â[r, s]`, entry `e = rℓ + s`. -/
abbrev aP (e : Nat) : Ptr := sc (oP e)
/-- `s₁ ‖ s₂`, entry `r`. -/
abbrev sP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + r))
abbrev tP (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k))
abbrev t1P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 1))
abbrev t0P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 2))

/-- The eight KiB four-way sampler scratch follows the live polynomials. -/
def oR4 (p : Params) : Nat := oP (p.k*p.ℓ+p.ℓ+p.k+3)

/-- The length of a packed polynomial of `s₁` or `s₂`, `32 · bitlen (2η)`. -/
def lenS (p : Params) : Nat := 32 * bitlen (2 * p.η)
/-- Where `t₀` starts in `sk`. -/
def oT0 (p : Params) : Nat := 128 + lenS p * (p.ℓ + p.k)

/-! ## The pieces -/

/-- `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the seed of `RejNTTPoly`, and
`ρ′ ‖ 0` to that of `RejBoundedPoly`. -/
def seedsWith (p : Params) : Prog isa :=
  .seq (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ))
    (.seq ((shake256With c) [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩] [⟨.x28, oHX, 128⟩])
      (.block (copy32 .x28 oHX .x28 oSA ++ copy32 .x28 (oHX + 32) .x28 oSB ++
        copy32 .x28 (oHX + 64) .x28 (oSB + 32) ++ setB (sc (oSB + 65)) 0)))

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`. -/
def expA (P : Prims) (p : Params) (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ)))
    (WindowMask.sampled (rejNttAt P (sc oSS) (sc oSA) (aP e)) (aP e))

/-- Copy rho to one 34-byte seed, allowing the unaligned seed stride. -/
def copySeed4 (j : Nat) : List Instr :=
  lea .x10 .x28 (oSA4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oSA .x10 0

def setSR (p : Params) (e j : Nat) : List Instr :=
  setB (sc (oSA4+34*j+32)) ((e+j)%p.ℓ) ++ setB (sc (oSA4+34*j+33)) ((e+j)/p.ℓ)

def seedSlot4 (p : Params) (e j : Nat) : Prog isa :=
  .seq (.block (copySeed4 j)) (.block (setSR p e j))

def expA4 (P : Prims) (p : Params) (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (WindowMask.mask4 (aP (4*g)))))

def expAll (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (expA4 P p) 0 (p.k*p.ℓ/4))
    (seqR (expA P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

/-- Entry `r` of `s₁ ‖ s₂`: `RejBoundedPoly(ρ′ ‖ r ‖ 0)`. -/
def expS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 64)) r))
    (WindowMask.sampled (rejBoundedAt P (sc oSS) (sc oSB) p.η (sP p r)) (sP p r))

/-- `ρ` to `pk` and `sk`, and `K` to `sk`. -/
def copies : List Instr :=
  copy32 .x28 oHX .x26 0 ++ copy32 .x28 oHX .x27 0 ++ copy32 .x28 (oHX + 96) .x27 32

/-- Entry `r` of `s₁ ‖ s₂`, packed to `sk`. -/
def packS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  bitPackAt P (sP p r) p.η p.η (.x27, 128 + lenS p * r) (lenS p)

/-- `ŝ₁[j] = NTT(s₁[j])`. -/
def nttS (P : Prims) (p : Params) (j : Nat) : Prog isa := nttAt P (sc oSS) (sP p j)

/-- Row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, and its `t₁` to `pk` and `t₀` to `sk`. -/
def row (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  .seq (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0))
    (.seq (seqR (fun j => mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) 1 (p.ℓ - 1))
    (.seq (invNttAt P (sc oSS) (tP p)) (.seq (addAt P (tP p) (sP p (p.ℓ + i)))
    (.seq (power2RoundAt P (tP p) (t1P p) (t0P p))
    (.seq (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320)
      (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416))))))

/-- `tr = H(pk, 64)` to `sk`. -/
def trHashWith (p : Params) : Prog isa := (shake256With c) [⟨.x26, 0, p.pkLen⟩] [⟨.x27, 64, 64⟩]

/-- Everything after the samplers. -/
def restWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block copies) (.seq (seqR (packS P p) 0 (p.ℓ + p.k)) (.seq (seqR (nttS P p) 0 p.ℓ)
    (.seq (seqR (row P p) 0 p.k) ((trHashWith c) p))))

/-- `vg_mldsa*_keygen` for the parameter set `p`, calling the primitives `P`. -/
def keyGenWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq ((seedsWith c) p) (.seq (expAll P p)
    (.seq (seqR (expS P p) 0 (p.ℓ + p.k)) (.seq ((restWith c) P p) (.block epi)))))

def seeds := seedsWith .scalar
def trHash := trHashWith .scalar
def rest := restWith .scalar
def keyGen := keyGenWith .scalar

end WindowKeygen


/-!
# ML-DSA on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify P p (pk = x0, mu = x1, sig = x2, scratch = x3) -> w0`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the SHA-3 sponge functions (`KeyGen/Frag.lean`).
It keeps `pk` in `x25`, `mu` in `x26`, `sig` in `x27` and `scratch` in
`x28`, and its result so far in `x24`.

The layout of `scratch` (in bytes) is that of key generation where they
share a buffer: the Keccak state at 0 and the sponge functions' working
space at 200, the saved registers at 840; the recomputed commitment hash
`c̃′` at 1024 (`oCT`, at most 64 bytes); the seed of `RejNTTPoly` at 1152
(`oSA`, 34 bytes); the working space of the primitives at 2048 (2048
bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is
polynomial `rℓ + s`, and after them come `w1Encode(w′₁)` (at most 1024
bytes), the hint `h` (`k` polynomials), `z` (`ℓ`), `c`, two temporaries, `w′`
and `w′₁`.

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ`
   (`vg_mldsa_hint_bit_unpack`); `x24` is its result, and it returns 0 at
   once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ`, and
   `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to the seed, `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (key generation's `expA`), and `c = SampleInBall(c̃)`. Each sampler's
   result is ANDed into `x24`, and its output masked with it (`sampled`):
   a sampler that fails leaves its output unspecified, and masking makes it
   reduced (zero) without a branch on the result, which is not a function
   of the inputs when it fails.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))`, `w′₁ = UseHint(h[r], w′)`,
   and its `SimpleBitPack` to `w1Encode(w′₁)`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`, and `x24 ← 0` unless `c̃′ = c̃`, without
   a branch.

It returns `x24`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak), and not on
the results of the samplers.
-/

namespace WindowVerify

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Spec.MlDsa (Params bitlen q)

section
variable (p : Params)

/-- The length of a packed `z[i]`, `32(1 + bitlen (γ₁ - 1))` bytes. -/
def lenZ : Nat := 32 * (1 + bitlen (p.γ₁ - 1))

/-- The offset of the hint in the signature. -/
def oHint : Nat := p.ctildeLen + lenZ p * p.ℓ

/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
def w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1

/-- The length of a packed `w₁[i]`, `32 · bitlen b`. -/
def w1Len : Nat := 32 * bitlen (w1Max p)

/-! ## The layout of the working space -/

/-- `c̃′`. -/
def oCT : Nat := 1024

/-- The polynomial `j` after `Â`. -/
abbrev vP (j : Nat) : Ptr := sc (oP (p.k * p.ℓ + j))

/-- `w1Encode(w′₁)` (at most 1024 bytes), first, so that its offset is below 2¹⁶, which the sponge takes. -/
abbrev bP : Ptr := vP p 0
abbrev hP (r : Nat) : Ptr := vP p (1 + r)
abbrev zP (i : Nat) : Ptr := vP p (1 + p.k + i)
abbrev cP : Ptr := vP p (1 + p.k + p.ℓ)
abbrev tmP : Ptr := vP p (1 + p.k + p.ℓ + 1)
abbrev tm2P : Ptr := vP p (1 + p.k + p.ℓ + 2)
abbrev wP : Ptr := vP p (1 + p.k + p.ℓ + 3)
abbrev w1P : Ptr := vP p (1 + p.k + p.ℓ + 4)

end

/-! ## The comparison -/

/-- One byte of `a ⊕ b` ORed into `x10`. -/
def cmpBody : List Instr :=
  [.ldrb .x9 .x0 0, .ldrb .x11 .x1 0, .logic .eor .x .x9 .x9 .x11, .logic .orr .x .x10 .x10 .x9,
    .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- `x24 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `x10` is the OR of the XORs of their bytes, so 0 exactly when they
are equal, and `(x10 - 1) >> 63` then 1, and 0 otherwise. -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.x0, .ptr a), (.x1, .ptr b), (.x2, .imm n)] ++ ([.movz .x .x10 0 0] : List Instr)))
    (.seq (.loop (.block cmpBody) (.nonzero .x .x2))
      (.block [.subImm .x .x10 .x10 1, .lsr .x .x10 .x10 63, .logic .and .w .x24 .x24 .x10]))

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `h`, and `x24 ←` the result. -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.x27, oHint p) (p.ω + p.k) p.ω (hP p 0) (256 * p.k)) (.block and24)

/-- `z[i]`, and `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p i))
    (.seq (normLtAt P (zP p i) (p.γ₁ - p.β)) (.block and24))

/-- `ρ` to the seed, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (.block (copy32 .x25 0 .x28 oSA)) (.seq (WindowKeygen.expAll P p)
    (WindowMask.sampled (ballAt P (sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) (cP p)))

/-- `Σₛ Â[r, s] ẑ[s]` to `w′`. -/
def dot (r : Nat) : Prog isa :=
  let _ := P
  CombDot.dotAt p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0)

/-- Row `r` of `w′`, `w′₁`, packed to `w1Encode(w′₁)`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) (.seq (nttAt P (sc oSS) (tmP p))
    (.seq (mulAt P (tm2P p) (cP p) (tmP p)) (.seq (subAt P (wP p) (tm2P p)) (.seq (invNttAt P (sc oSS) (wP p))
      (.seq (useHintAt P (hP p r) (wP p) p.γ₂ (w1P p))
        (simpleBitPackAt P (w1P p) (w1Max p) ((bP p).1, (bP p).2 + w1Len p * r) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def computeWith : Prog isa :=
  .seq (seqR (fun i => nttAt P (sc oSS) (zP p i)) 0 p.ℓ) (.seq (nttAt P (sc oSS) (cP p))
    (.seq (seqR (row P p) 0 p.k)
    (.seq ((shake256With c) [⟨.x26, 0, 64⟩, ⟨.x28, (bP p).2, p.k * w1Len p⟩] [⟨.x28, oCT, p.ctildeLen⟩])
      (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen))))

def bodyWith : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) ((computeWith c) P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verifyWith : Prog isa := .seq (.block pro) (.seq ((bodyWith c) P p) (.block epi))

end

def compute := computeWith .scalar
def body := bodyWith .scalar
def verify := verifyWith .scalar

end WindowVerify

def main : IO Unit := do
 for (suffix,callee) in [("scalar",Impl.Sha3.AArch64.Callee.scalar),("sha3",VG.Variants.Keccak.AArch64.Sha3.variant.callee)] do
  let prims := VG.Impl.MlDsa.AArch64.KeyGen.primsWith callee
  for (name,p) in [("44",Spec.MlDsa.mlDsa44),("65",Spec.MlDsa.mlDsa65),("87",Spec.MlDsa.mlDsa87)] do
   let code := printer.function (WindowVerify.verifyWith callee prims p)
   IO.FS.writeFile ("/tmp/vg-window-verify"++name++"-mask-dot-"++suffix++".body") (String.join (code.map (Rust.line printer.call)))
