module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen

/-!
# ML-DSA on AArch64: pieces of `vg_mldsa{44,65,87}_sign`

The constants of a parameter set `p`, the layout of `scratch`, and pieces of
code, as calls of the primitives `P` and the sponge functions (`Frag.lean`),
from which the signing functions (`Optimized.signWith`,
`Sign/OptimizedRest.lean`) are built: `ML-DSA.Sign_internal(sk, M′, rnd)`
(FIPS 204 Algorithm 7) with the message representative `μ` given
(`Spec.MlDsa.signMu`). They keep `scratch` in `x28`, `sk` in `x25`, `mu` in
`x26`, `rnd` in `x27` and `sig` in `x23`. Signing goes:

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params bitlen q)

/-! ## The constants of a parameter set -/

section
variable (p : Params)

/-- `λ/4`, the length of `c̃`. -/
abbrev cLen : Nat := p.ctildeLen
/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
abbrev w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1
/-- The length of the encoding of a polynomial of `w₁`. -/
abbrev w1Len : Nat := 32 * bitlen (w1Max p)
/-- The length of the encoding of a polynomial of `z`. -/
abbrev zLen : Nat := 32 * (1 + bitlen (p.γ₁ - 1))
/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev sLen : Nat := 32 * bitlen (2 * p.η)

/-- The offsets of `s₁[r]`, `s₂[i]` and `t₀[i]` in `sk`. -/
abbrev skS1 (r : Nat) : Nat := 128 + sLen p * r
abbrev skS2 (i : Nat) : Nat := 128 + sLen p * p.ℓ + sLen p * i
abbrev skT0 (i : Nat) : Nat := 128 + sLen p * (p.ℓ + p.k) + 416 * i

/-- The offsets of `z[r]` and of the hint in `sig`. -/
abbrev sigZ (r : Nat) : Nat := cLen p + zLen p * r
abbrev sigH : Nat := cLen p + zLen p * p.ℓ

/-! ## The polynomials of the working space

`ĉ` (0), four temporaries (1–4), then `h` (`k`), `y` (`ℓ`), `ŷ` (`ℓ`),
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row). -/

abbrev pS (i : Nat) : Ptr := sc (oP i)
abbrev cP : Ptr := pS 0
abbrev t1P : Ptr := pS 1
abbrev t2P : Ptr := pS 2
abbrev t3P : Ptr := pS 3
abbrev t4P : Ptr := pS 4
abbrev hP (i : Nat) : Ptr := pS (5 + i)
abbrev yP (r : Nat) : Ptr := pS (5 + p.k + r)
abbrev yhP (r : Nat) : Ptr := pS (5 + p.k + p.ℓ + r)
abbrev wP (i : Nat) : Ptr := pS (5 + p.k + 2 * p.ℓ + i)
abbrev s1P (r : Nat) : Ptr := pS (5 + 2 * p.k + 2 * p.ℓ + r)
abbrev s2P (i : Nat) : Ptr := pS (5 + 2 * p.k + 3 * p.ℓ + i)
abbrev t0P (i : Nat) : Ptr := pS (5 + 3 * p.k + 3 * p.ℓ + i)
abbrev aP (i j : Nat) : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- Scratch for the four simultaneous SHAKE streams, after the matrix. -/
def oR4 : Nat := oP (5+4*p.k+3*p.ℓ+p.k*p.ℓ)

def seedSlot4 (e j : Nat) : Prog isa :=
  .seq (.block (lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0))
    (.block (setB (sc (oRS4+34*j+32)) ((e+j)%p.ℓ) ++ setB (sc (oRS4+34*j+33)) ((e+j)/p.ℓ)))

def sample4 (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      [(.x0,.ptr (sc oRS4)),(.x1,.ptr (pS (5+4*p.k+3*p.ℓ+4*g))),(.x2,.ptr (sc (oR4 p)))]) (.block and24))

def sampleAll : Prog isa :=
  .seq (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (seqR (sampleE P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

/-- `ρ` to four seed slots, and matrix expansion in batches of four. -/
def expandA : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) (sampleAll P p)

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`, through `x9`. -/
def setKappa (r : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 r, .strb .x9 .x28 (oMS + 64), .lsr .x .x9 .x9 8,
    .strb .x9 .x28 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (.seq (copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))))

/-- Paired-mask seed staging in the unused prefix gap. -/
def oMP : Nat := 1632

def maskSeedHalf (src dst : Nat) : List Instr :=
  lea .x10 .x28 dst ++ Impl.MlKem.AArch64.copy32 .x28 src .x10 0

def maskPairNonce (r j : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (r+j),
    .strb .x9 .x28 (oMP+66*j+64),.lsr .x .x9 .x9 8,.strb .x9 .x28 (oMP+66*j+65)]

def maskPairSeed (r j : Nat) : Prog isa :=
  .seq (.block (maskSeedHalf oMS (oMP+66*j)))
    (.seq (.block (maskSeedHalf (oMS+32) (oMP+66*j+32))) (.block (maskPairNonce r j)))

/-- Finish a mask whose canonical coefficients have already been sampled. -/
def maskFinish (r : Nat) : Prog isa :=
  .seq (copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))

/-- Two independent standard mask samples share the paired SHAKE engine.
The old matrix-sampler workspace is dead throughout this phase. -/
def maskPairR (nm : String) (cd : Prog isa) (r : Nat) : Prog isa :=
  .seq (maskPairSeed r 0) (.seq (maskPairSeed r 1)
    (.seq (callAt nm cd [(.x0,.ptr (sc oMP)),(.x1,.imm p.γ₁),
      (.x2,.ptr (yP p r)),(.x3,.ptr (yP p (r+1))),(.x4,.ptr (sc (oR4 p)))])
      (.seq (maskFinish P p r) (maskFinish P p (r+1)))))

def masksPaired (nm : String) (cd : Prog isa) : Prog isa :=
  .seq (seqR (fun j => maskPairR P p nm cd (2*j)) 0 (p.ℓ/2))
    (seqR (maskR P p) (2*(p.ℓ/2)) (p.ℓ%2))

/-- Paired SHA3 path, with the original single-stream fallback. -/
def masks : Prog isa :=
  if P.pairedMask then masksPaired P p "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair
  else seqR (maskR P p) 0 p.ℓ

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  callAt (if p.γ₂ = 261888 then "vg_mldsa_high_pack4" else "vg_mldsa_high_pack6")
    (P.highPack p.γ₂) [(.x0,.ptr (wP p i)),(.x1,.ptr (sc (oW1+w1Len p*i)))]

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])` and its norm, `w[i] - cs₂[i] + ct₀[i]` (in `w[i]`),
`-ct₀[i]` (in `T4`), and `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hR (i : Nat) : Prog isa :=
  .seq (mulAt P t3P cP (t0P p i)) (.seq (invNttAt P t3P) (.seq (normAt P t3P p.γ₂)
    (.seq (copy t4P (wP p i) 1024) (.seq (addAt P (wP p i) t3P) (.seq (subAt P t4P (wP p i))
      (makeHintAt P t4P (wP p i) p.γ₂ (hP i)))))))

/-- `x24 ← x24 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.ldr .x .x9 .x28 oONES, .subImm .x .x9 .x9 (p.ω + 1), .lsr .x .x9 .x9 63, .logic .and .w .x24 .x24 .x9]

/-- `KAP ← KAP + ℓ`, through `x9`. -/
def kapAdd : List Instr := [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 p.ℓ, .str .x .x9 .x28 oKAP]

/-- `CNT ← CNT - 1`, left in `x9`, which the loop tests. -/
def cntDec : List Instr := [.ldr .x .x9 .x28 oCNT, .subImm .x .x9 .x9 1, .str .x .x9 .x28 oCNT]

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.x23, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copy (.x23, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)))

end

end VG.Impl.MlDsa.AArch64.Sign
