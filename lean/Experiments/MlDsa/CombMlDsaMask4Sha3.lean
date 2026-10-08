import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace CombCopy
open VG.Impl.MlDsa.AArch64.Call
-- Disjoint source/destination regions as in copyChk; handle all lengths, including zero.
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
 .seq (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2)) <|
 .seq (if n/8=0 then .block [] else
  .seq (.block (movV .x2 (n/8)))
   (.loop (.block [.ldr .x .x9 .x1 0,.str .x .x9 .x0 0,
    .addImm .x .x0 .x0 8,.addImm .x .x1 .x1 8,.subImm .x .x2 .x2 1]) (.nonzero .x .x2)))
  (.block ((List.range (n%8)).flatMap fun j => [.ldrb .x9 .x1 j,.strb .x9 .x0 j]))
end CombCopy
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

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

namespace CombMask4
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def pro : List Instr :=
 (List.range 10).map (fun i => .str .x (saved[i]!) .x3 (7968+8*i)) ++
 (List.range 8).flatMap (fun i => [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x3 (8048+8*i)]) ++
 [.str .w .x1 .x3 7904,mov .x19 .x3,mov .x20 .x0,mov .x21 .x2]
def epi : List Instr :=
 (List.range 8).flatMap (fun i => [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) ++
 (List.range 9).map (fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i)) ++
 [.ldr .x .x19 .x19 7968]
def seedWord (j : Nat) : List Instr :=
 [.ldr .x .x6 .x3 (8*j),.ldr .x .x7 .x4 (8*j),.vop (.dup .d2 .v0 .x6),
  .vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 (16*j)]
def lastWord (r n : Reg) : List Instr :=
 [.ldrb r n 64,.ldrb .x8 n 65,.lsl .x .x8 .x8 8,.add .x r r .x8]
def absorb (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66] ++
 (List.range 8).flatMap seedWord ++ lastWord .x6 .x3 ++ lastWord .x7 .x4 ++
 [.movz .x .x9 31 1,.add .x .x6 .x6 .x9,.add .x .x7 .x7 .x9,
  .vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 128,
  .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 256]
def setup : List Instr :=
 [mov .x22 .x19,.addImm .x .x23 .x19 400,.addImm .x .x24 .x19 840,
  .addImm .x .x25 .x19 1520,.addImm .x .x26 .x19 2200,.addImm .x .x27 .x19 2880,
  .movz .x .x28 5 0]
def squeeze (a b : Reg) : List Instr :=
 (List.range 17).flatMap fun i => [.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,
  .str .x .x6 a (8*i),.str .x .x7 b (8*i)]
def pair (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p)) <|
 .seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg true 24) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p ++ squeeze a b)
def step : Prog isa := .seq (pair .x22 .x24 .x25) <| .seq (pair .x23 .x26 .x27) <|
 .block [.addImm .x .x24 .x24 136,.addImm .x .x25 .x25 136,
 .addImm .x .x26 .x26 136,.addImm .x .x27 .x27 136,.subImm .x .x28 .x28 1]
def unpack (c k : Nat) : Prog isa :=
 .seq (.block ([.addImm .x .x2 .x19 (840+680*k),.addImm .x .x3 .x21 (1024*k),
   .movz .x .x5 64 0,.movz .x .x8 (BitVec.ofNat 16 (2^(c-16)-1)) 1,
   .movk .x .x8 0xffff 0] ++ movQ .x9))
 (.loop (.block (emBody c)) (.nonzero .x .x5))
def unpack4 (c : Nat) : Prog isa := .seq (unpack c 0) <| .seq (unpack c 1) <| .seq (unpack c 2) (unpack c 3)
def prog : Prog isa :=
 .seq (.block (pro ++ Rej4.zeroStates ++ absorb 0 ++ absorb 1 ++ setup)) <|
 .seq (.loop step (.nonzero .x .x28)) <|
 .seq (.block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]) <|
 .seq (.ite (.zero .x .x9) (unpack4 18) (unpack4 20)) (.block epi)
end CombMask4
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

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

namespace CombSignMask4
open VG.Impl.MlDsa.AArch64.Sign

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

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decodeWith : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    ((shakeAtWith c) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`, through `x9`. -/
def setKappa (r : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 r, .strb .x9 .x28 (oMS + 64), .lsr .x .x9 .x9 8,
    .strb .x9 .x28 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (.seq (CombCopy.copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (mulAt P (wP p i) (aP p i 0) (yhP p 0))
    (.seq (seqR (fun j => mulAddAt P (wP p i) (aP p i j) (yhP p j)) 1 (p.ℓ - 1)) (invNttAt P (wP p i)))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

def mask4Seed (g j : Nat) : Prog isa :=
 .seq (CombCopy.copy (sc (1632+66*j)) (sc oMS) 64) <|
 .block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (4*g+j),
  .strb .x9 .x28 (1632+66*j+64),.lsr .x .x9 .x9 8,.strb .x9 .x28 (1632+66*j+65)]
def mask4Group (g : Nat) : Prog isa :=
 .seq (seqR (mask4Seed g) 0 4) <|
 .seq (.block (glue [(.x0,.ptr (sc 1632)),(.x1,.imm p.γ₁),
   (.x2,.ptr (yP p (4*g))),(.x3,.ptr (sc (oR4 p)))])) <|
 .seq CombMask4.prog <|
 seqR (fun j => .seq (CombCopy.copy (yhP p j) (yP p j) 1024) (nttAt P (yhP p j))) (4*g) 4

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commitWith : Prog isa :=
  .seq (.seq (seqR (mask4Group P p) 0 (p.ℓ/4)) (seqR (maskR P p) (4*(p.ℓ/4)) (p.ℓ%4))) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    ((shakeAtWith c) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩)))

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` (in `y[r]`), and its norm. -/
def zR (r : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s1P p r)) (.seq (invNttAt P t1P) (.seq (addAt P (yP p r) t1P)
    (normAt P (yP p r) (p.γ₁ - p.β))))

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` (in `w[i]`), and the norm of its `LowBits`. -/
def r0R (i : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s2P p i)) (.seq (invNttAt P t1P) (.seq (subAt P (wP p i) t1P)
    (.seq (lowBitsAt P (wP p i) p.γ₂ t2P) (normAt P t2P (p.γ₂ - p.β)))))

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])` and its norm, `w[i] - cs₂[i] + ct₀[i]` (in `w[i]`),
`-ct₀[i]` (in `T4`), and `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hR (i : Nat) : Prog isa :=
  .seq (mulAt P t3P cP (t0P p i)) (.seq (invNttAt P t3P) (.seq (normAt P t3P p.γ₂)
    (.seq (CombCopy.copy t4P (wP p i) 1024) (.seq (addAt P (wP p i) t3P) (.seq (subAt P t4P (wP p i))
      (makeHintAt P t4P (wP p i) p.γ₂ (hP i)))))))

/-- `x24 ← x24 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.ldr .x .x9 .x28 oONES, .subImm .x .x9 .x9 (p.ω + 1), .lsr .x .x9 .x9 63, .logic .and .w .x24 .x24 .x9]

/-- `KAP ← KAP + ℓ`, through `x9`. -/
def kapAdd : List Instr := [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 p.ℓ, .str .x .x9 .x28 oKAP]

/-- The validity checks of an iteration, combined into `x24`; then, if they
passed, `CNT ← 1` (the loop ends with `w24 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block ([.movz .x .x24 1 0] ++ setQ (sc oONES) 0))
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))))))))

/-- `CNT ← CNT - 1`, left in `x9`, which the loop tests. -/
def cntDec : List Instr := [.ldr .x .x9 .x28 oCNT, .subImm .x .x9 .x9 1, .str .x .x9 .x28 oCNT]

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `x24 ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`. -/
def iterWith : Prog isa :=
  .seq ((commitWith c) P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) (checks P p) (.block ([.movz .x .x24 0 0] ++ setQ (sc oCNT) 1)))
      (.block cntDec)))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoopWith : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) (.loop ((iterWith c) P p) (.nonzero .x .x9))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.x23, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (CombCopy.copy (.x23, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def restWith : Prog isa := .seq ((decodeWith c) P p) (.seq ((signLoopWith c) P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def signWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk ((restWith c) P p)) (.block epi)))

def decode := decodeWith .scalar
def commit := commitWith .scalar
def iter := iterWith .scalar
def signLoop := signLoopWith .scalar
def rest := restWith .scalar
def sign := signWith .scalar

end CombSignMask4


def main : IO Unit := do
 let callee := VG.Variants.Keccak.AArch64.Sha3.variant.callee
 let prims := Proof.MlDsa.AArch64.Sign.primsWith callee
 let pm := printer.function CombMask4.prog
 IO.FS.writeFile "/tmp/comb-expand_mask4_sha3.body" (String.join (pm.map (Rust.line printer.call)))
 for (name,p) in [("44",Spec.MlDsa.mlDsa44),("65",Spec.MlDsa.mlDsa65),("87",Spec.MlDsa.mlDsa87)] do
  let code := printer.function (CombSignMask4.signWith callee prims p)
  IO.FS.writeFile ("/tmp/comb-sign"++name++"-mask4-copy8_sha3.body") (String.join (code.map (Rust.line printer.call)))
  IO.println s!"sign{name}-mask4-copy8_sha3: {code.length}"
