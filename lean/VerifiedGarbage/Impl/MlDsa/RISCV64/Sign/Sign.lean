module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Frag
public import VerifiedGarbage.Impl.MlDsa.RISCV64.CacheCopy
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: `vg_mldsa44_sign_with_cache`, `vg_mldsa65_sign_with_cache`, `vg_mldsa87_sign_with_cache`

As on PPC64LE (`Impl/MlDsa/PPC64LE/Sign/Sign.lean`), on the pieces of key
generation (`KeyGen/Frag.lean`).

`sign P p (sk = a0, mu = a1, rnd = a2, sig = a3, scratch = a4, cache = a5,
cache_len = a6) -> a0`, the kernel `vg_mldsa*_sign` and
`vg_mldsa*_sign_prepared` share (`PreparedKey/Entry.lean`):
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and of the sponge functions. It keeps
`scratch` in `s11`, `sk` in `s10`, `mu` in `s9` and `rnd` in `s8`, and
stores `sig` in `scratch` (at `SIG`), loading it into `s8` once `rnd` is no
longer needed; the AND of the results so far in `s4`; and, in the loop, the
iterations left in `s5`, the number of 1s of the hint in `s6` and the
counter `κ` in `s7`. It saves our caller's `s3`–`s11` and our return
address in `scratch`, as key generation does: callee-saved registers, which
the functions it calls preserve. Until step 2 it keeps in `s3` the cache, or
0 if `cache_len` is 0.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `s4` the
   AND of the results. If one failed (`s4 = 0`), it returns 0 at once.
2. `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, with `rnd ‖ μ` first copied to `W1`
   (so that the sponge reads one argument besides `scratch`, as its proof
   requires of arguments that may overlap), then `sig` to `s8`; and `ŝ₁`, `ŝ₂`
   and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of `sk`, or, with a
   cache, its bytes, copied a byte at a time (`CacheCopy.lean`), since the
   cache need not be aligned.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`):
   the commitment (`y ← ExpandMask(ρ″, κ)`, `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`,
   and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)` at `CT`), then
   `c = SampleInBall(c̃)` and, if it succeeded, the validity checks in order,
   stopping at the first failing `z` or `r₀` polynomial: the norms of
   `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `s4 = 0`), when the checks pass (`s4 = 1`), or after 814
   iterations.
4. If `s4 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branches on validity checks on which check rejected the iteration and,
for `z` and `r₀`, the first failing polynomial; and only the call of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Sign

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (hash copy topEnd)
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg callAt setB seqR and24)
open VG.Impl.Sha3.RISCV64.Stream (mov)
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

The Keccak state at 0, our caller's registers at 1288 (as ML-KEM's); `sig`
at 912 (`SIG`, 8 bytes); the
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
abbrev sc (off : Nat) : Ptr := (.s11, off)

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

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.a0, .ptr f), (.a1, .ptr (sc oPS))]

def invNttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_inv_ntt" P.invNtt [(.a0, .ptr f), (.a1, .ptr (sc oPS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def addAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_add" P.add [(.a0, .ptr f), (.a1, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.a0, .ptr f), (.a1, .ptr g)]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `s4 ← s4 ∧ result`. -/
def rejAt (a : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT [(.a0, .ptr (sc oRS)), (.a1, .ptr a), (.a2, .ptr (sc oPS))])
    (.block and24)

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_expand_mask_poly" P.expandMask
    [(.a0, .ptr (sc oMS)), (.a1, .imm gamma1), (.a2, .ptr a), (.a3, .ptr (sc oPS))]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`. -/
def ballAt (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball
    [(.a0, .ptr (sc oCT)), (.a1, .imm len), (.a2, .imm tau), (.a3, .ptr c), (.a4, .ptr (sc oPS))]

def highBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_high_bits" P.highBits [(.a0, .ptr r), (.a1, .imm gamma2), (.a2, .ptr out)]

def lowBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_low_bits" P.lowBits [(.a0, .ptr r), (.a1, .imm gamma2), (.a2, .ptr out)]

/-- `‖f‖∞ < bound`, and `s4 ← s4 ∧ result`. -/
def normAt (f : Ptr) (bound : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_norm_lt" P.normLt [(.a0, .ptr f), (.a1, .imm bound)]) (.block and24)

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s (the low word of
`a0`, zero-extended) added to `s6`. -/
def makeHintAt (z r : Ptr) (gamma2 : Nat) (h : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_make_hint" P.makeHint [(.a0, .ptr z), (.a1, .ptr r), (.a2, .imm gamma2), (.a3, .ptr h)])
    (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .add .s6 .s6 .a0])

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.a0, .ptr f), (.a1, .imm b), (.a2, .ptr out), (.a3, .imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_bit_pack" P.bitPack
    [(.a0, .ptr f), (.a1, .imm a), (.a2, .imm b), (.a3, .ptr out), (.a4, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.a0, .ptr v), (.a1, .imm len), (.a2, .imm a), (.a3, .imm b), (.a4, .ptr f)]

def hintBitPackAt (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_pack" P.hintBitPack
    [(.a0, .ptr h), (.a1, .imm hlen), (.a2, .imm omega), (.a3, .ptr y), (.a4, .imm len)]

end

/-! ## Branches, entry and exit -/

/-- `t` if `s4 ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa := .ite (.nonzero .s4) t e

/-- `c` if `s4 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-- Our caller's `s3`–`s11` and our return address saved in `scratch` (in
`a4`), the pointers moved to `s8`–`s11`, `sig` stored at `SIG`, and
`s4 ← 1`. -/
def pro : List Instr :=
  Impl.MlKem.RISCV64.topSave .a4 ++
    ([mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a4, .store .d .a3 .s11 oSIG, .li .s4 1,
      .li .t2 0, .sltu .t0 .t2 .a6, .sub .t0 .t2 .t0, .logic .and .s3 .a5 .t0] : List Instr)

/-- Run checks in order, stopping at the first failing polynomial. -/
def seqOk (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (f a) (ifOk (seqOk f (a+1) n))

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- `ρ` to `RS`, and the `kℓ` entries of `Â`. -/
def expandA : Prog isa := .seq (copy .s10 0 .s11 oRS 32) (seqR (sampleE P p) 0 (p.k * p.ℓ))

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, from `rnd ‖ μ` copied to `W1`, then `sig` to `s8`. -/
def rhoPP : Prog isa :=
  .seq (copy .s8 0 .s11 oW1 32) (.seq (copy .s9 0 .s11 (oW1 + 32) 64)
    (.seq (hash 136 0x1f [⟨.s10, 32, 32⟩, ⟨.s11, oW1, 96⟩] [⟨.s11, oMS, 64⟩]) (.block [.load .d .s8 .s11 oSIG])))

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.s10, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.s10, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.s10, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂` and `t̂₀`, decoded from `sk` and transformed. -/
def decodeKey : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (seqR (decT0 P p) 0 p.k))

/-- `ŝ₁`, `ŝ₂` and `t̂₀`, copied a byte at a time (the cache need not be
aligned) from the `ℓ + 2k` polynomials of the cache at `s3` to their slots,
which follow one another. -/
def cached : Prog isa := CacheCopy.cacheCopy 0 (s1P p 0) (1024 * (p.ℓ + 2 * p.k))

/-- `ρ″` and `sig`, then `ŝ₁`, `ŝ₂` and `t̂₀`: from the cache if `s3 ≠ 0`,
and otherwise from `sk`. -/
def decode : Prog isa :=
  .seq (rhoPP) (.ite (.nonzero .s3) (cached p) (decodeKey P p))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`. -/
def setKappa (r : Nat) : List Instr :=
  [.addi .a0 .s7 r, .store .b .a0 .s11 (oMS + 64), .shift .srl .d .a0 .a0 8, .store .b .a0 .s11 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r))
    (.seq (copy .s11 (oP (5 + p.k + r)) .s11 (oP (5 + p.k + p.ℓ + r)) 1024) (nttAt P (yhP p r))))

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
    (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oW1, p.k * w1Len p⟩] [⟨.s11, oCT, cLen p⟩])))

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
    (.seq (copy .s11 (oP 3) .s11 (oP 4) 1024) (.seq (subAt P t4P t3P) (.seq (subAt P t4P t3P)
      (.seq (addAt P (wP p i) t3P) (makeHintAt P t4P (wP p i) p.γ₂ (hP i))))))))

/-- `s4 ← s4 ∧ (s6 ≤ ω)`: `s6 - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.addi .a0 .s6 (-((p.ω + 1 : Nat) : Int)), .shift .srl .d .a0 .a0 63, .logic .and .s4 .s4 .a0]

/-- Stop the low-part phase at its first failed polynomial and skip hints. -/
def checksR0 : Prog isa :=
  .seq (seqOk (r0R P p) 0 p.k) (ifOk (.seq (seqR (hR P p) 0 p.k) (.block (onesOk p))))

/-- Reject at the first failing response or low-part polynomial. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block [.li .s4 1,.li .s6 0])
    (.seq (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p)))
      (ifOkElse (.block [.li .s5 1]) (.block [.addi .s7 .s7 p.ℓ]))))

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (its result, the low word of `a0`, zero-extended, is not zero; and
otherwise `s4 ← 0`, `s5 ← 1`); then `s5 ← s5 - 1`. -/
def iter : Prog isa :=
  .seq (commit P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.seq (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32])
      (.ite (.nonzero .a0) (checks P p) (.block [.li .s4 0, .li .s5 1]))) (.block [.addi .s5 .s5 (-1)])))

/-- The rejection sampling loop: `κ ← 0`, `s5 ← 814`, and iterations while
`s5 ≠ 0`. -/
def signLoop : Prog isa := .seq (.block [.li .s7 0, .li .s5 814]) (.loop (iter P p) (.nonzero .s5))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.s8, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copy .s11 oCT .s8 0 (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.s8, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def rest : Prog isa := .seq (decode P p) (.seq (signLoop P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def sign (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk (rest P p)) (.block topEnd)))

end VG.Impl.MlDsa.RISCV64.Sign
