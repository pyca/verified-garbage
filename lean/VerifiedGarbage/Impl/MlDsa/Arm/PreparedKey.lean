module

public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Frag
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: preparing keys

`vg_mldsa*_prepare_verifying_key(pk, prepared, scratch)` and
`vg_mldsa*_prepare_signing_key(sk, prepared, scratch)` copy the encoded key to
`prepared`, then write after it each of its polynomials in the NTT domain:
`NTT(t₁[i] · 2ᵈ)` of a public key, `NTT(s₁)`, `NTT(s₂)` and `NTT(t₀)` of a
private key, each unpacked into its place in `prepared` and transformed
there, with `scratch` the working space of the NTT.

As the signing function does (`Sign/Frag.lean`), they keep the address of
each buffer in a callee-saved register: the key in `r4`, `prepared` in `r8`
and `scratch` in `r7`. These and `lr` are saved in one frame (`entry`),
whose pop restores `r4`, after `r7`, `r8` and `lr` are loaded back from it.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.PreparedKey

open VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr Arg callR callS copy seqR)

/-- `body` with the key in `r4`, `prepared` in `r8` and `scratch` in `r7`, in
a frame saving our caller's `r4`, `r7`, `r8` and `lr`. -/
def entry (body : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r7, .r8, .lr])
    (.seq (.block [.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)])
      (.seq body (.seq (.block [.ldrSp .r7 4]) (.seq (.block [.ldrSp .r8 8]) (.block [.ldrSp .lr 12])))))
    (.pop .r4 16)

/-- `NTT` of the polynomial at `offset` in `prepared`, in place. -/
def transform (P : Prims) (offset : Nat) : Prog isa :=
  callR "vg_mldsa_ntt" P.ntt [.ptr (.r8, offset), .ptr (.r7, 0)]

/-- `NTT(t₁[i] · 2ᵈ)` of the public key, to its place in `prepared`. -/
def publicPoly (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  .seq (callR "vg_mldsa_unpack_t1" Pack.unpackT1 [.ptr (.r4, 32 + 320 * i), .ptr (.r8, p.pkLen + 1024 * i)])
    (transform P (p.pkLen + 1024 * i))

/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
def secretLen (p : Params) : Nat := 32 * bitlen (2 * p.η)

/-- Where polynomial `i` of `s₁ ‖ s₂ ‖ t₀` is in the private key, its length,
and the bounds of its coefficients. -/
def secretPiece (p : Params) (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then (128 + secretLen p * i, secretLen p, p.η, p.η)
  else (128 + secretLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k), 416, 4095, 4096)

/-- Polynomial `i` of `NTT(s₁) ‖ NTT(s₂) ‖ NTT(t₀)` of the private key, to its
place in `prepared`. -/
def secretPoly (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  let (offset, len, a, b) := secretPiece p i
  .seq (callS "vg_mldsa_bit_unpack" P.bitUnpack
      [.ptr (.r4, offset), .imm len, .imm a, .imm b, .ptr (.r8, p.skLen + 1024 * i)])
    (transform P (p.skLen + 1024 * i))

/-- `vg_mldsa*_prepare_verifying_key(pk = r0, prepared = r1, scratch = r2)`. -/
def preparePublic (P : Prims) (p : Params) : Prog isa :=
  entry (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly P p) 0 p.k))

/-- `vg_mldsa*_prepare_signing_key(sk = r0, prepared = r1, scratch = r2)`. -/
def prepareSecret (P : Prims) (p : Params) : Prog isa :=
  entry (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k)))

end VG.Impl.MlDsa.Arm.PreparedKey
