module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Frag
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Spec.MlDsa.PreparedKey

/-!
# ML-DSA on PPC64LE: `vg_mldsa{44,65,87}_prepare_{signing,verifying}_key`

`prepare(key = r3, prepared = r4, scratch = r5)` copies the encoded key to
`prepared` (its whole doublewords, with the gathers' loop: every encoded
key's length is a multiple of 8), then, for each polynomial `i` of the key,
unpacks it from that copy to `prepared + keyLen + 1024 i` and transforms it
there with `vg_mldsa_ntt` (working space `scratch`): `BitUnpack` of `s₁`,
`s₂` (`η`) and `t₀` (`2¹² - 1`, `2¹²`) for a private key, `t₁ · 2ᵈ`
(`vg_mldsa_unpack_t1`) for a public key. It keeps `prepared` in `r30` and
`scratch` in `r31`, in frames saving them, and the link register (moved to
`r0`) in a frame. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.PreparedKey

open VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Spec.MlDsa

/-- `body` with `prepared` (`r4`) in `r30` and `scratch` (`r5`) in `r31`, in
the frames saving them and the link register, and with the encoded key's
`len / 8` doublewords (at `r3`) copied to `prepared` first. -/
def prepareFrame (len : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (.frame (.push .r30) (.frame (.push .r31)
    (.seq (.block [mov .r30 .r4, mov .r31 .r5, mov .r9 .r4, .li .r5 (len / 8)])
      (.seq Impl.Gather.PPC64LE.copyWords body)) (.pop .r31)) (.pop .r30)) (.pop .r0)) (.block [.mtlr .r0]))

/-- The `NTT` of the polynomial at `prepared + off`. -/
def transform (off : Nat) : Prog isa :=
  callAt "vg_mldsa_ntt" Arith.ntt [(.r3, .ptr (.r30, off)), (.r4, .ptr (.r31, 0))]

/-- The length of a polynomial of `s₁` or `s₂`. -/
abbrev secretLen (p : Params) : Nat := 32 * bitlen (2 * p.η)

/-- Polynomial `i` of a private key: its offset and length in the key, and
the bounds of `BitUnpack`. -/
def secretPiece (p : Params) (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then (128 + secretLen p * i, secretLen p, p.η, p.η)
  else (128 + secretLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k), 416, 4095, 4096)

/-- Polynomial `i` of a private key. -/
def secretPoly (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_bit_unpack" Pack.bitUnpack
      [(.r3, .ptr (.r30, (secretPiece p i).1)), (.r4, .imm (secretPiece p i).2.1),
        (.r5, .imm (secretPiece p i).2.2.1), (.r6, .imm (secretPiece p i).2.2.2),
        (.r7, .ptr (.r30, p.skLen + 1024 * i))])
    (transform (p.skLen + 1024 * i))

/-- Polynomial `i` of a public key. -/
def publicPoly (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_unpack_t1" Pack.unpackT1
      [(.r3, .ptr (.r30, 32 + 320 * i)), (.r4, .ptr (.r30, p.pkLen + 1024 * i))])
    (transform (p.pkLen + 1024 * i))

/-- `vg_mldsa*_prepare_signing_key`. -/
def prepareSecret (p : Params) : Prog isa := prepareFrame p.skLen (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k))

/-- `vg_mldsa*_prepare_verifying_key`. -/
def preparePublic (p : Params) : Prog isa := prepareFrame p.pkLen (seqR (publicPoly p) 0 p.k)

end VG.Impl.MlDsa.PPC64LE.PreparedKey
