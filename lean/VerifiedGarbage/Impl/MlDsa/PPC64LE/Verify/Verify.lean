module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on PPC64LE: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

As on 32-bit ARM (`Impl/MlDsa/Arm/Verify/Verify.lean`).

`verify P p (pk = r3, mu = r4, sig = r5, scratch = r6) -> r3`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the sponge functions. Its entry and exit are key
generation's (`KeyGen/Frag.lean`), so it keeps `pk` in `r30`, `mu` in `r29`,
`sig` in `r28`, `scratch` in `r31`, and its result so far in `r24`, and saves
our caller's `r24`–`r31` and our return address in `scratch`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200, the saved registers at 840 (as ML-KEM's);
the seed of `RejNTTPoly` (`SB`, 34 bytes) at 920; `w1Encode(w′₁)` at 1024
(at most 1024 bytes); the recomputed commitment hash `c̃′` at 2048 (at most
64 bytes); the working space of the primitives at 4096 (2048 bytes); and
polynomials of 1024 bytes from 8192 (`oP j`): the hint `h` (polynomials 0 to
7, of which the first `k`), `z` (8 to 14), `c` (15), two temporaries (16,
17), `w′` (18), `w′₁` (19), and `Â[r, s]` (`20 + 8r + s`).

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ` to polynomials
   `0, …, k - 1` (`vg_mldsa_hint_bit_unpack`); `r24` is its result, and it
   returns 0 at once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ` (polynomial `8 + i`), and
   `r24 ← r24 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to `SB`, and `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (polynomial `20 + 8r + s`); `c = SampleInBall(c̃)` (polynomial 15). Each
   sampler's result is ANDed into `r24`, and its output masked with it
   (`sampled`).
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))` (polynomial 18),
   `w′₁ = UseHint(h[r], w′)` (polynomial 19), and its `SimpleBitPack` to
   `1024 + r · 32 bitlen b`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `2048`, and `r24 ← 0` unless
   `c̃′ = c̃`, without a branch.

It returns `r24`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak) and not on
the results of the samplers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Verify

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (hash copy topEnd cmpBody)
open VG.Impl.MlDsa.PPC64LE.KeyGen (Ptr Arg callAt setB seqR and24 sampled pro)
open VG.Spec.MlDsa

/-- The code of the primitives `vg_mldsa_*` that verification calls. -/
structure Prims where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  sub : Prog isa
  rejNtt : Prog isa
  ball : Prog isa
  useHint : Prog isa
  simpleBitPack : Prog isa
  bitUnpack : Prog isa
  unpackT1 : Prog isa
  hintUnpack : Prog isa
  normLt : Prog isa

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

end

/-! ## The layout of the working space -/

def oSB : Nat := 920
def oB : Nat := 1024
def oCT : Nat := 2048
def oSS : Nat := 4096
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 8192 + 1024 * j

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.r31, off)

/-- Polynomial `j` of the working space. -/
abbrev pS (j : Nat) : Ptr := sc (oP j)

abbrev pH (r : Nat) : Ptr := pS r
abbrev pZ (i : Nat) : Ptr := pS (8 + i)
abbrev pC : Ptr := pS 15
abbrev pT : Ptr := pS 16
abbrev pT2 : Ptr := pS 17
abbrev pW : Ptr := pS 18
abbrev pW1 : Ptr := pS 19
abbrev pA (r s : Nat) : Ptr := pS (20 + 8 * r + s)

/-! ## The primitives -/

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.r3, .ptr f), (.r4, .ptr (sc oSS))]

def invNttAt (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_inv_ntt" P.invNtt [(.r3, .ptr f), (.r4, .ptr (sc oSS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.r3, .ptr h), (.r4, .ptr f), (.r5, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.r3, .ptr h), (.r4, .ptr f), (.r5, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.r3, .ptr f), (.r4, .ptr g)]

def rejNttAt (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_ntt_poly" P.rejNtt [(.r3, .ptr (sc oSB)), (.r4, .ptr a), (.r5, .ptr (sc oSS))]

def ballAt (ct : Ptr) (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball
    [(.r3, .ptr ct), (.r4, .imm len), (.r5, .imm tau), (.r6, .ptr c), (.r7, .ptr (sc oSS))]

def useHintAt (h r : Ptr) (g2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_use_hint" P.useHint [(.r3, .ptr h), (.r4, .ptr r), (.r5, .imm g2), (.r6, .ptr out)]

def sbpAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.r3, .ptr f), (.r4, .imm b), (.r5, .ptr out), (.r6, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.r3, .ptr v), (.r4, .imm len), (.r5, .imm a), (.r6, .imm b), (.r7, .ptr f)]

def unpackT1At (v f : Ptr) : Prog isa :=
  callAt "vg_mldsa_unpack_t1" P.unpackT1 [(.r3, .ptr v), (.r4, .ptr f)]

def hintUnpackAt (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_unpack" P.hintUnpack
    [(.r3, .ptr y), (.r4, .imm len), (.r5, .imm omega), (.r6, .ptr h), (.r7, .imm hlen)]

def normLtAt (f : Ptr) (bound : Nat) : Prog isa :=
  callAt "vg_mldsa_norm_lt" P.normLt [(.r3, .ptr f), (.r4, .imm bound)]

end

/-! ## Control -/

/-- `c` if `r24 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := .ite (.nonzero .d .r24) c (.block [])

/-- `r24 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `r12` is the OR of the XORs of their bytes (ML-KEM's `cmpBody`, with
`r26` counting down), so 0 exactly when they are equal, and then
`(r12 - 1) >> 63` is 1 (and 0 otherwise, as `r12 < 256`). -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (Arg.instrs .r3 (.ptr a) ++ Arg.instrs .r4 (.ptr b) ++ Arg.instrs .r26 (.imm n) ++
      ([.li .r12 0] : List Instr)))
    (.seq (.loop (.block cmpBody) (.nonzero .d .r26))
      (.block [.subi .r12 .r12 1, .lsr .d .r12 .r12 63, .logic .and .r24 .r24 .r12]))

/-! ## The function -/

section
variable (P : Prims) (p : Params)

/-- `h` to polynomials `0, …, k - 1`, and `r24 ←` the result (`r24` is 1
before). -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.r28, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) (.block and24)

/-- `z[i]`, and `r24 ← r24 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r28, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ i))
    (.seq (normLtAt P (pZ i) (p.γ₁ - p.β)) (.block and24))

/-- `Â[r, s]`, entry `e = 8r + s`. -/
def aOne (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) (e % 8) ++ setB (sc (oSB + 33)) (e / 8)))
    (sampled (rejNttAt P (pS (20 + e))) (pS (20 + e)))

/-- The entries `8r + s` of row `r` of `Â`. -/
def aRow (r : Nat) : Prog isa := seqR (aOne P) (8 * r) p.ℓ

/-- `ρ` to `SB`, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (copy .r30 0 .r31 oSB 32) (.seq (seqR (aRow P p) 0 p.k)
    (sampled (ballAt P (.r28, 0) p.ctildeLen p.τ pC) pC))

/-- `Σₛ Â[r, s] ẑ[s]` to `W`. -/
def dot (r : Nat) : Prog isa :=
  .seq (mulAt P pW (pA r 0) (pZ 0)) (seqR (fun s => mulAddAt P pW (pA r s) (pZ s)) 1 (p.ℓ - 1))

/-- Row `r` of `w′`, `w′₁`, packed to `B`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.r30, 32 + 320 * r) pT) (.seq (nttAt P pT)
    (.seq (mulAt P pT2 pC pT) (.seq (subAt P pW pT2) (.seq (invNttAt P pW)
      (.seq (useHintAt P (pH r) pW p.γ₂ pW1) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def compute : Prog isa :=
  .seq (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (.seq (nttAt P pC) (.seq (seqR (row P p) 0 p.k)
    (.seq (hash 136 0x1f [⟨.r29, 0, 64⟩, ⟨.r31, oB, p.k * w1Len p⟩] [⟨.r31, oCT, p.ctildeLen⟩])
      (cmpAnd (sc oCT) (.r28, 0) p.ctildeLen))))

def body : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verify : Prog isa := .seq (.block pro) (.seq (body P p) (.block topEnd))

end

end VG.Impl.MlDsa.PPC64LE.Verify
