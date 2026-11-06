module

public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa{44,65,87}_prepare_signing_key` and `_prepare_verifying_key`

`prepare(key, prepared, scratch)`: leaves, with `scratch` (argument 2, 1024
bytes, the working space of `vg_mldsa_ntt`) in `esi`, that copy the encoded
key to the start of `prepared` and write after it, as `u32` coefficients,
the polynomials signing or verification computes from it, each the `NTT` of
a piece of the key unpacked in place:

* a private key: `ŝ₁`, `ŝ₂` (`BitUnpack(·, η, η)` of their pieces) and `t̂₀`
  (`BitUnpack(·, 2ᵈ⁻¹ - 1, 2ᵈ⁻¹)`), `ℓ + 2k` polynomials;
* a public key: `t̂₁[r]` (`vg_mldsa_unpack_t1`, which multiplies by `2ᵈ`),
  `k` polynomials.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.PreparedKey

open VG.X86
open VG.Impl.MlKem.X86 (Buf leaf copyW at_)
open VG.Impl.MlDsa.X86.KeyGen (callP seqR)
open VG.Impl.MlDsa.X86.Verify (Prims)
open VG.Spec.MlDsa (Params bitlen)

section
variable (P : Prims) (p : Params)

/-- Polynomial `i` of `prepared`, after a key of `kl` bytes. -/
abbrev slot (kl i : Nat) : Buf := ⟨1, kl + 1024 * i, 1024⟩

/-- `esi ← scratch`, then the key copied to the start of `prepared`. -/
def start (kl : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * 2)))])
    (copyW 2 ⟨0, 0, 4 * (kl / 4)⟩ ⟨1, 0, 4 * (kl / 4)⟩ (kl / 4))

/-- Polynomial `i` of `prepared`, transformed in place. -/
def nttSlot (kl i : Nat) : Prog isa := callP 2 "vg_mldsa_ntt" P.ntt [.buf (slot kl i), .buf ⟨2, 0, 1024⟩]

/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev sLen : Nat := 32 * bitlen (2 * p.η)

/-- The offset, length and bounds of the piece of `sk` of polynomial `i`. -/
def secretPiece (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then (128 + sLen p * i, sLen p, p.η, p.η)
  else (128 + sLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k), 416, 4095, 4096)

/-- Polynomial `i` of a prepared private key. -/
def secretPoly (i : Nat) : Prog isa :=
  .seq (callP 2 "vg_mldsa_bit_unpack" P.bitUnpack
      [.buf ⟨0, (secretPiece p i).1, (secretPiece p i).2.1⟩, .imm (secretPiece p i).2.1, .imm (secretPiece p i).2.2.1,
        .imm (secretPiece p i).2.2.2, .buf (slot p.skLen i)])
    (nttSlot P p.skLen i)

/-- Polynomial `r` of a prepared public key. -/
def publicPoly (r : Nat) : Prog isa :=
  .seq (callP 2 "vg_mldsa_unpack_t1" P.unpackT1 [.buf ⟨0, 32 + 320 * r, 320⟩, .buf (slot p.pkLen r)])
    (nttSlot P p.pkLen r)

/-- `vg_mldsa{44,65,87}_prepare_signing_key`, with the primitives `P`. -/
def prepareSecret : Prog isa := leaf (.seq (start p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k)))

/-- `vg_mldsa{44,65,87}_prepare_verifying_key`, with the primitives `P`. -/
def preparePublic : Prog isa := leaf (.seq (start p.pkLen) (seqR (publicPoly P p) 0 p.k))

end

end VG.Impl.MlDsa.X86.PreparedKey
