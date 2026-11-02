module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

As on PPC64LE (`Impl/MlDsa/PPC64LE/Verify/Verify.lean`).

`verify P p (pk = a0, mu = a1, sig = a2, scratch = a3) -> a0`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the sponge functions. Its entry and exit are key
generation's (`KeyGen/Frag.lean`), so it keeps `pk` in `s10`, `mu` in `s9`,
`sig` in `s8`, `scratch` in `s11`, and its result so far in `s4`, and saves
our caller's `s3`–`s11` and our return address in `scratch` (at 1288,
`oSave`).

The layout of `scratch` (in bytes): the Keccak state at 0, the seed of
`RejNTTPoly` (`SB`, 34 bytes) at 920, the saved registers at 1288 (as
ML-KEM's); `w1Encode(w′₁)` at 2048 (at most 1024 bytes); the recomputed
commitment hash `c̃′` at 3072 (at most 64 bytes); the working space of the
primitives at 4096 (2048 bytes); and polynomials of 1024 bytes from 8192
(`oP j`): the hint `h` (polynomials 0 to 7, of which the first `k`), `z`
(8 to 14), `c` (15), two temporaries (16, 17), `w′` (18), `w′₁` (19), and
`Â[r, s]` (`20 + 8r + s`). Every buffer is at a multiple of 8.

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ` to polynomials
   `0, …, k - 1` (`vg_mldsa_hint_bit_unpack`); `s4` is its result, and it
   returns 0 at once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ` (polynomial `8 + i`), and
   `s4 ← s4 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to `SB`, and `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (polynomial `20 + 8r + s`); `c = SampleInBall(c̃)` (polynomial 15). Each
   sampler's result is ANDed into `s4`, and its output masked with it
   (`sampled`).
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))` (polynomial 18),
   `w′₁ = UseHint(h[r], w′)` (polynomial 19), and its `SimpleBitPack` to
   `2048 + r · 32 bitlen b`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `3072`, and `s4 ← 0` unless
   `c̃′ = c̃`, without a branch.

It returns `s4`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak) and not on
the results of the samplers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Verify

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (hash copy topEnd cmpBody)
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg callAt setB seqR and24 sampled pro)
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
def oB : Nat := 2048
def oCT : Nat := 3072
def oSS : Nat := 4096
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 8192 + 1024 * j

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.s11, off)

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

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.a0, .ptr f), (.a1, .ptr (sc oSS))]

def invNttAt (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_inv_ntt" P.invNtt [(.a0, .ptr f), (.a1, .ptr (sc oSS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.a0, .ptr f), (.a1, .ptr g)]

def rejNttAt (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_ntt_poly" P.rejNtt [(.a0, .ptr (sc oSB)), (.a1, .ptr a), (.a2, .ptr (sc oSS))]

def ballAt (ct : Ptr) (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball
    [(.a0, .ptr ct), (.a1, .imm len), (.a2, .imm tau), (.a3, .ptr c), (.a4, .ptr (sc oSS))]

def useHintAt (h r : Ptr) (g2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_use_hint" P.useHint [(.a0, .ptr h), (.a1, .ptr r), (.a2, .imm g2), (.a3, .ptr out)]

def sbpAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.a0, .ptr f), (.a1, .imm b), (.a2, .ptr out), (.a3, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.a0, .ptr v), (.a1, .imm len), (.a2, .imm a), (.a3, .imm b), (.a4, .ptr f)]

def unpackT1At (v f : Ptr) : Prog isa :=
  callAt "vg_mldsa_unpack_t1" P.unpackT1 [(.a0, .ptr v), (.a1, .ptr f)]

def hintUnpackAt (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_unpack" P.hintUnpack
    [(.a0, .ptr y), (.a1, .imm len), (.a2, .imm omega), (.a3, .ptr h), (.a4, .imm hlen)]

def normLtAt (f : Ptr) (bound : Nat) : Prog isa :=
  callAt "vg_mldsa_norm_lt" P.normLt [(.a0, .ptr f), (.a1, .imm bound)]

end

/-! ## Control -/

/-- `c` if `s4 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := .ite (.nonzero .s4) c (.block [])

/-- `s4 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `t2` is the OR of the XORs of their bytes (ML-KEM's `cmpBody`, with
`s6` counting down), so 0 exactly when they are equal, and then
`(t2 - 1) >> 63` is 1 (and 0 otherwise, as `t2 < 256`). -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (Arg.instrs .a0 (.ptr a) ++ Arg.instrs .a1 (.ptr b) ++ Arg.instrs .s6 (.imm n) ++
      ([.li .t2 0] : List Instr)))
    (.seq (.loop (.block cmpBody) (.nonzero .s6))
      (.block [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .logic .and .s4 .s4 .t2]))

/-! ## The function -/

section
variable (P : Prims) (p : Params)

/-- `h` to polynomials `0, …, k - 1`, and `s4 ←` the result (`s4` is 1
before). -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.s8, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) (.block and24)

/-- `z[i]`, and `s4 ← s4 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.s8, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ i))
    (.seq (normLtAt P (pZ i) (p.γ₁ - p.β)) (.block and24))

/-- `Â[r, s]`, entry `e = 8r + s`. -/
def aOne (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) (e % 8) ++ setB (sc (oSB + 33)) (e / 8)))
    (sampled (rejNttAt P (pS (20 + e))) (pS (20 + e)))

/-- The entries `8r + s` of row `r` of `Â`. -/
def aRow (r : Nat) : Prog isa := seqR (aOne P) (8 * r) p.ℓ

/-- `ρ` to `SB`, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (copy .s10 0 .s11 oSB 32) (.seq (seqR (aRow P p) 0 p.k)
    (sampled (ballAt P (.s8, 0) p.ctildeLen p.τ pC) pC))

/-- `Σₛ Â[r, s] ẑ[s]` to `W`. -/
def dot (r : Nat) : Prog isa :=
  .seq (mulAt P pW (pA r 0) (pZ 0)) (seqR (fun s => mulAddAt P pW (pA r s) (pZ s)) 1 (p.ℓ - 1))

/-- Row `r` of `w′`, `w′₁`, packed to `B`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.s10, 32 + 320 * r) pT) (.seq (nttAt P pT)
    (.seq (mulAt P pT2 pC pT) (.seq (subAt P pW pT2) (.seq (invNttAt P pW)
      (.seq (useHintAt P (pH r) pW p.γ₂ pW1) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def compute : Prog isa :=
  .seq (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (.seq (nttAt P pC) (.seq (seqR (row P p) 0 p.k)
    (.seq (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] [⟨.s11, oCT, p.ctildeLen⟩])
      (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen))))

def body : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verify : Prog isa := .seq (.block pro) (.seq (body P p) (.block topEnd))

end

end VG.Impl.MlDsa.RISCV64.Verify
