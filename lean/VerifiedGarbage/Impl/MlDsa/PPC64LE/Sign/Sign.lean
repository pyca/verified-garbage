module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on PPC64LE: `vg_mldsa44_sign`, `vg_mldsa65_sign`, `vg_mldsa87_sign`

As on 32-bit ARM (`Impl/MlDsa/Arm/Sign/Sign.lean`), on the pieces of key
generation (`KeyGen/Frag.lean`).

`sign P p (sk = r3, mu = r4, rnd = r5, sig = r6, scratch = r7) -> r3`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and of the sponge functions. It keeps
`scratch` in `r31`, `sk` in `r30`, `mu` in `r29` and `rnd` in `r28`, and
stores `sig` in `scratch` (at `SIG`), loading it into `r28` once `rnd` is no
longer needed; the AND of the results so far in `r24`; and, in the loop, the
iterations left in `r25`, the number of 1s of the hint in `r26` and the
counter `κ` in `r27`. It saves our caller's `r24`–`r31` and our return
address in `scratch`, as key generation does: callee-saved registers, which
the functions it calls preserve.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `r24` the
   AND of the results. If one failed (`r24 = 0`), it returns 0 at once.
2. `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, with `rnd ‖ μ` first copied to `W1`
   (so that the sponge reads one argument besides `scratch`, as its proof
   requires of arguments that may overlap), then `sig` to `r28`; and `ŝ₁`, `ŝ₂`
   and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of `sk`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`):
   the commitment (`y ← ExpandMask(ρ″, κ)`, `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`,
   and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)` at `CT`), then
   `c = SampleInBall(c̃)` and, if it succeeded, every validity check of the
   iteration, combined without a branch into `r24`: the norms of
   `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `r24 = 0`), when the checks pass (`r24 = 1`), or after 814
   iterations.
4. If `r24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sign

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (hash copy topEnd)
open VG.Impl.MlDsa.PPC64LE.KeyGen (Ptr Arg callAt setB seqR and24)
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Spec.MlDsa (Params bitlen q)

/-- The code of the polynomial primitives that signing calls. -/
structure Prims where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  add : Prog isa
  sub : Prog isa
  rejNTT : Prog isa
  expandMask : Prog isa
  ball : Prog isa
  highBits : Prog isa
  lowBits : Prog isa
  normLt : Prog isa
  makeHint : Prog isa
  simpleBitPack : Prog isa
  bitPack : Prog isa
  bitUnpack : Prog isa
  hintBitPack : Prog isa

/-! ## The layout of the working space (in bytes)

The Keccak state at 0 and the sponge functions' working space at 200, our
caller's registers at 840 (as ML-KEM's); `sig` at 912 (`SIG`, 8 bytes); the
seed of `RejNTTPoly` (`RS`, 34 bytes) at 920; the seed of `ExpandMask` (`MS`,
`ρ″` and two bytes) at 960; `c̃` (`CT`, up to 64 bytes) at 1040; the
encoding of `w₁` (`W1`, up to 1024 bytes) at 2048; the working space of the
primitives (`PS`, 2048 bytes) at 3072; and polynomials of 1024 bytes from
5120 (`P i`). -/

def oSIG : Nat := 912
def oRS : Nat := 920
def oMS : Nat := 960
def oCT : Nat := 1040
def oW1 : Nat := 2048
def oPS : Nat := 3072
/-- Polynomial `i`. -/
def oP (i : Nat) : Nat := 5120 + 1024 * i

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.r31, off)

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

/-! ## The polynomial primitives

Each takes its working space (if any) at `PS`. -/

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.r3, .ptr f), (.r4, .ptr (sc oPS))]

def invNttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_inv_ntt" P.invNtt [(.r3, .ptr f), (.r4, .ptr (sc oPS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.r3, .ptr h), (.r4, .ptr f), (.r5, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.r3, .ptr h), (.r4, .ptr f), (.r5, .ptr g)]

def addAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_add" P.add [(.r3, .ptr f), (.r4, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.r3, .ptr f), (.r4, .ptr g)]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `r24 ← r24 ∧ result`. -/
def rejAt (a : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT [(.r3, .ptr (sc oRS)), (.r4, .ptr a), (.r5, .ptr (sc oPS))])
    (.block and24)

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_expand_mask_poly" P.expandMask
    [(.r3, .ptr (sc oMS)), (.r4, .imm gamma1), (.r5, .ptr a), (.r6, .ptr (sc oPS))]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`. -/
def ballAt (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball
    [(.r3, .ptr (sc oCT)), (.r4, .imm len), (.r5, .imm tau), (.r6, .ptr c), (.r7, .ptr (sc oPS))]

def highBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_high_bits" P.highBits [(.r3, .ptr r), (.r4, .imm gamma2), (.r5, .ptr out)]

def lowBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_low_bits" P.lowBits [(.r3, .ptr r), (.r4, .imm gamma2), (.r5, .ptr out)]

/-- `‖f‖∞ < bound`, and `r24 ← r24 ∧ result`. -/
def normAt (f : Ptr) (bound : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_norm_lt" P.normLt [(.r3, .ptr f), (.r4, .imm bound)]) (.block and24)

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s (the low word of
`r3`) added to `r26`. -/
def makeHintAt (z r : Ptr) (gamma2 : Nat) (h : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_make_hint" P.makeHint [(.r3, .ptr z), (.r4, .ptr r), (.r5, .imm gamma2), (.r6, .ptr h)])
    (.block [.lsr .w .r3 .r3 0, .add .r26 .r26 .r3])

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.r3, .ptr f), (.r4, .imm b), (.r5, .ptr out), (.r6, .imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_bit_pack" P.bitPack
    [(.r3, .ptr f), (.r4, .imm a), (.r5, .imm b), (.r6, .ptr out), (.r7, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.r3, .ptr v), (.r4, .imm len), (.r5, .imm a), (.r6, .imm b), (.r7, .ptr f)]

def hintBitPackAt (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_pack" P.hintBitPack
    [(.r3, .ptr h), (.r4, .imm hlen), (.r5, .imm omega), (.r6, .ptr y), (.r7, .imm len)]

end

/-! ## Branches, entry and exit -/

/-- `t` if `r24 ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa := .ite (.nonzero .d .r24) t e

/-- `c` if `r24 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-- Our caller's `r24`–`r31` and our return address saved in `scratch` (in
`r7`), the pointers moved to `r28`–`r31`, `sig` stored at `SIG`, and
`r24 ← 1`. -/
def pro : List Instr :=
  Impl.MlKem.PPC64LE.topSave .r7 ++
    ([mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r31 .r7, .store .d .r6 .r31 oSIG, .li .r24 1] : List Instr)

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- `ρ` to `RS`, and the `kℓ` entries of `Â`. -/
def expandA : Prog isa := .seq (copy .r30 0 .r31 oRS 32) (seqR (sampleE P p) 0 (p.k * p.ℓ))

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, from `rnd ‖ μ` copied to `W1`, then `sig` to `r28`. -/
def rhoPP : Prog isa :=
  .seq (copy .r28 0 .r31 oW1 32) (.seq (copy .r29 0 .r31 (oW1 + 32) 64)
    (.seq (hash 136 0x1f [⟨.r30, 32, 32⟩, ⟨.r31, oW1, 96⟩] [⟨.r31, oMS, 64⟩]) (.block [.load .d .r28 .r31 oSIG])))

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r30, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r30, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r30, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ρ″` and `sig`, then `ŝ₁`, `ŝ₂` and `t̂₀`. -/
def decode : Prog isa :=
  .seq (rhoPP) (.seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (seqR (decT0 P p) 0 p.k)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`. -/
def setKappa (r : Nat) : List Instr :=
  [.addi .r3 .r27 r, .stb .r3 .r31 (oMS + 64), .lsr .d .r3 .r3 8, .stb .r3 .r31 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r))
    (.seq (copy .r31 (oP (5 + p.k + r)) .r31 (oP (5 + p.k + p.ℓ + r)) 1024) (nttAt P (yhP p r))))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (mulAt P (wP p i) (aP p i 0) (yhP p 0))
    (.seq (seqR (fun j => mulAddAt P (wP p i) (aP p i j) (yhP p j)) 1 (p.ℓ - 1)) (invNttAt P (wP p i)))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commit : Prog isa :=
  .seq (seqR (maskR P p) 0 p.ℓ) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    (hash 136 0x1f [⟨.r29, 0, 64⟩, ⟨.r31, oW1, p.k * w1Len p⟩] [⟨.r31, oCT, cLen p⟩])))

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` (in `y[r]`), and its norm. -/
def zR (r : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s1P p r)) (.seq (invNttAt P t1P) (.seq (addAt P (yP p r) t1P)
    (normAt P (yP p r) (p.γ₁ - p.β))))

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` (in `w[i]`), and the norm of its `LowBits`. -/
def r0R (i : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s2P p i)) (.seq (invNttAt P t1P) (.seq (subAt P (wP p i) t1P)
    (.seq (lowBitsAt P (wP p i) p.γ₂ t2P) (normAt P t2P (p.γ₂ - p.β)))))

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])` and its norm, `-ct₀[i] = (ct₀[i] - ct₀[i]) - ct₀[i]`
(in `T4`; the slots of `w` are too far into `scratch` for `copy`'s offsets),
`w[i] - cs₂[i] + ct₀[i]` (in `w[i]`), and `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hR (i : Nat) : Prog isa :=
  .seq (mulAt P t3P cP (t0P p i)) (.seq (invNttAt P t3P) (.seq (normAt P t3P p.γ₂)
    (.seq (copy .r31 (oP 3) .r31 (oP 4) 1024) (.seq (subAt P t4P t3P) (.seq (subAt P t4P t3P)
      (.seq (addAt P (wP p i) t3P) (makeHintAt P t4P (wP p i) p.γ₂ (hP i))))))))

/-- `r24 ← r24 ∧ (r26 ≤ ω)`: `r26 - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.subi .r3 .r26 (p.ω + 1), .lsr .d .r3 .r3 63, .logic .and .r24 .r24 .r3]

/-- The validity checks of an iteration, combined into `r24`; then, if they
passed, `r25 ← 1` (the loop ends with `r24 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block [.li .r24 1, .li .r26 0])
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block [.li .r25 1]) (.block [.addi .r27 .r27 p.ℓ])))))))

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `r24 ← 0`, `r25 ← 1`); then `r25 ← r25 - 1`. -/
def iter : Prog isa :=
  .seq (commit P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .r3) (checks P p) (.block [.li .r24 0, .li .r25 1])) (.block [.subi .r25 .r25 1])))

/-- The rejection sampling loop: `κ ← 0`, `r25 ← 814`, and iterations while
`r25 ≠ 0`. -/
def signLoop : Prog isa := .seq (.block [.li .r27 0, .li .r25 814]) (.loop (iter P p) (.nonzero .d .r25))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.r28, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copy .r31 oCT .r28 0 (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.r28, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def rest : Prog isa := .seq (decode P p) (.seq (signLoop P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def sign (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk (rest P p)) (.block topEnd)))

end VG.Impl.MlDsa.PPC64LE.Sign
