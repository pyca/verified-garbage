module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

As on PPC64LE (`Impl/MlDsa/PPC64LE/KeyGen/KeyGen.lean`).
`keyGen P p (seed = a0, pk = a1, sk = a2, scratch = a3) -> a0`:
`ML-DSA.KeyGen_internal(ξ)` (FIPS 204 Algorithm 6) of the parameter set
`p`, with `ξ` at `seed`, as calls of the primitives `P` and of the SHA-3
sponge functions. It keeps `seed` in `s10`, `pk` in `s9`, `sk` in `s8`,
`scratch` in `s11` and the AND of the results of the samplers in `s4`, and
saves our caller's `s3`–`s11` and our return address in `scratch`
(`Frag.lean`).

The layout of `scratch` (in bytes): the Keccak state at 0, the saved
registers at 1288 (as ML-KEM's);
`k` and `ℓ` at 920 (`oKL`); `(ρ, ρ′, K)` at 1024 (`oHX`, 128 bytes); the
seed of `RejNTTPoly` at 1152 (`oSA`, 34 bytes) and of `RejBoundedPoly` at
1216 (`oSB`, 66 bytes); the working space of the primitives at 2048
(2048 bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]`
is polynomial `rℓ + s`, `s₁[j]` (then `ŝ₁[j]`) polynomial `kℓ + j`,
`s₂[i]` polynomial `kℓ + ℓ + i`, and `t`, `t₁` and `t₀` the three after
them.

1. `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, and `ρ` and `ρ′` to the seeds.
2. `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` and `s₁ ‖ s₂ = RejBoundedPoly(ρ′ ‖ r ‖ 0)`
   (`ExpandA`, `ExpandS`). After each, `s4 ← s4 ∧ result`, and the
   polynomial is ANDed with `-result` (`mask`): it is zero if the sampler
   failed, so that every polynomial is reduced, and small, whatever the
   samplers return, without a branch.
3. `ρ` and `K` to `sk`; `s₁` and `s₂`, `BitPack`ed, to `sk`; `ŝ₁ = NTT(s₁)`.
4. For each row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, `Power2Round`, and
   `t₁` `SimpleBitPack`ed to `pk`, `t₀` `BitPack`ed to `sk`; `ρ` to `pk`.
5. `tr = H(pk, 64)` to `sk`; return `s4`.

Every address and branch depends only on the pointers, but for what the
samplers leak (`ρ` and which half-bytes `RejBoundedPoly` rejects).
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.KeyGen

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (hash copy topEnd)
open VG.Spec.MlDsa (Params bitlen)

/-- The code of the primitives key generation calls. -/
structure Prims where
  /-- `vg_mldsa_ntt` -/
  ntt : Prog isa
  /-- `vg_mldsa_inv_ntt` -/
  invNtt : Prog isa
  /-- `vg_mldsa_multiply_ntt` -/
  mul : Prog isa
  /-- `vg_mldsa_multiply_add_ntt` -/
  mulAdd : Prog isa
  /-- `vg_mldsa_add` -/
  add : Prog isa
  /-- `vg_mldsa_rej_ntt_poly` -/
  rejNtt : Prog isa
  /-- `vg_mldsa_rej_bounded_poly` -/
  rejBounded : Prog isa
  /-- `vg_mldsa_power2round` -/
  power2Round : Prog isa
  /-- `vg_mldsa_simple_bit_pack` -/
  simpleBitPack : Prog isa
  /-- `vg_mldsa_bit_pack` -/
  bitPack : Prog isa

/-! ## The layout of the working space -/

def oKL : Nat := 920
def oHX : Nat := 1024
def oSA : Nat := 1152
def oSB : Nat := 1216
def oSS : Nat := 2048
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 4096 + 1024 * j

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.s11, off)
/-- `Â[r, s]`, entry `e = rℓ + s`. -/
abbrev aP (e : Nat) : Ptr := sc (oP e)
/-- `s₁ ‖ s₂`, entry `r`. -/
abbrev sP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + r))
abbrev tP (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k))
abbrev t1P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 1))
abbrev t0P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 2))

/-- The length of a packed polynomial of `s₁` or `s₂`, `32 · bitlen (2η)`. -/
def lenS (p : Params) : Nat := 32 * bitlen (2 * p.η)
/-- Where `t₀` starts in `sk`. -/
def oT0 (p : Params) : Nat := 128 + lenS p * (p.ℓ + p.k)

/-! ## Calls of the primitives -/

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.a0, .ptr f), (.a1, .ptr (sc oSS))]

def invNttAt (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_inv_ntt" P.invNtt [(.a0, .ptr f), (.a1, .ptr (sc oSS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]

def addAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_add" P.add [(.a0, .ptr f), (.a1, .ptr g)]

def rejNttAt (seed a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_ntt_poly" P.rejNtt [(.a0, .ptr seed), (.a1, .ptr a), (.a2, .ptr (sc oSS))]

def rejBoundedAt (seed : Ptr) (eta : Nat) (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_bounded_poly" P.rejBounded
    [(.a0, .ptr seed), (.a1, .imm eta), (.a2, .ptr a), (.a3, .ptr (sc oSS))]

def power2RoundAt (t t1 t0 : Ptr) : Prog isa :=
  callAt "vg_mldsa_power2round" P.power2Round [(.a0, .ptr t), (.a1, .ptr t1), (.a2, .ptr t0)]

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.a0, .ptr f), (.a1, .imm b), (.a2, .ptr out), (.a3, .imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_bit_pack" P.bitPack
    [(.a0, .ptr f), (.a1, .imm a), (.a2, .imm b), (.a3, .ptr out), (.a4, .imm len)]

end

/-! ## The pieces -/

/-- `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the seed of `RejNTTPoly`, and
`ρ′ ‖ 0` to that of `RejBoundedPoly`. -/
def seeds (p : Params) : Prog isa :=
  .seq (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ))
    (.seq (hash 136 0x1f [⟨.s10, 0, 32⟩, ⟨.s11, oKL, 2⟩] [⟨.s11, oHX, 128⟩])
      (.seq (copy .s11 oHX .s11 oSA 32) (.seq (copy .s11 (oHX + 32) .s11 oSB 64) (.block (setB (sc (oSB + 65)) 0)))))

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`. -/
def expA (P : Prims) (p : Params) (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ)))
    (sampled (rejNttAt P (sc oSA) (aP e)) (aP e))

/-- Entry `r` of `s₁ ‖ s₂`: `RejBoundedPoly(ρ′ ‖ r ‖ 0)`. -/
def expS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 64)) r)) (sampled (rejBoundedAt P (sc oSB) p.η (sP p r)) (sP p r))

/-- `ρ` to `pk` and `sk`, and `K` to `sk`. -/
def copies : Prog isa :=
  .seq (copy .s11 oHX .s9 0 32) (.seq (copy .s11 oHX .s8 0 32) (copy .s11 (oHX + 96) .s8 32 32))

/-- Entry `r` of `s₁ ‖ s₂`, packed to `sk`. -/
def packS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  bitPackAt P (sP p r) p.η p.η (.s8, 128 + lenS p * r) (lenS p)

/-- `ŝ₁[j] = NTT(s₁[j])`. -/
def nttS (P : Prims) (p : Params) (j : Nat) : Prog isa := nttAt P (sP p j)

/-- Row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, and its `t₁` to `pk` and `t₀` to `sk`. -/
def row (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  .seq (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0))
    (.seq (seqR (fun j => mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) 1 (p.ℓ - 1))
    (.seq (invNttAt P (tP p)) (.seq (addAt P (tP p) (sP p (p.ℓ + i)))
    (.seq (power2RoundAt P (tP p) (t1P p) (t0P p))
    (.seq (simpleBitPackAt P (t1P p) 1023 (.s9, 32 + 320 * i) 320)
      (bitPackAt P (t0P p) 4095 4096 (.s8, oT0 p + 416 * i) 416))))))

/-- `tr = H(pk, 64)` to `sk`, absorbing `pk` in two pieces: its first 1024
bytes, then the rest, since the length of a piece is an immediate of 12 bits
(`spongeArgs`). -/
def trHash (p : Params) : Prog isa := hash 136 0x1f [⟨.s9, 0, 1024⟩, ⟨.s9, 1024, p.pkLen - 1024⟩] [⟨.s8, 64, 64⟩]

/-- Everything after the samplers. -/
def rest (P : Prims) (p : Params) : Prog isa :=
  .seq copies (.seq (seqR (packS P p) 0 (p.ℓ + p.k)) (.seq (seqR (nttS P p) 0 p.ℓ)
    (.seq (seqR (row P p) 0 p.k) (trHash p))))

/-- `vg_mldsa*_keygen` for the parameter set `p`, calling the primitives `P`. -/
def keyGen (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (seeds p) (.seq (seqR (expA P p) 0 (p.k * p.ℓ))
    (.seq (seqR (expS P p) 0 (p.ℓ + p.k)) (.seq (rest P p) (.block topEnd)))))

end VG.Impl.MlDsa.RISCV64.KeyGen
