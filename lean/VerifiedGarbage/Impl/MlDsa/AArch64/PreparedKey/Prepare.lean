module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-! # Prepare canonical, backend-independent ML-DSA key-polynomial caches -/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.Call

def prepareFrame (body : Prog isa) : Prog isa :=
  [Reg.x25, .x26, .x28, .x30].foldr
    (fun r body => .frame (.push r) body (.pop r))
    (.seq (.block [.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0,
      .addImm .x .x28 .x2 0]) body)

def transform (offset : Nat) : Prog isa :=
  callAt "vg_mldsa_ntt" Arith.Neon.ntt
    [(.x0, .ptr (.x26, offset)), (.x1, .ptr (.x28, 0))]

def publicPoly (p : Params) (i : Nat) : Prog isa :=
  .seq
    (callAt "vg_mldsa_unpack_t1" Pack.unpackT1
      [(.x0, .ptr (.x25, 32 + 320 * i)),
        (.x1, .ptr (.x26, p.pkLen + 1024 * i))])
    (transform (p.pkLen + 1024 * i))

def secretLen (p : Params) : Nat := 32 * bitlen (2 * p.η)

def secretPiece (p : Params) (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then
    (128 + secretLen p * i, secretLen p, p.η, p.η)
  else
    (128 + secretLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k),
      416, 4095, 4096)

def secretPoly (p : Params) (i : Nat) : Prog isa :=
  let (offset, len, a, b) := secretPiece p i
  .seq
    (callAt "vg_mldsa_bit_unpack" Pack.bitUnpack
      [(.x0, .ptr (.x25, offset)), (.x1, .imm len), (.x2, .imm a),
        (.x3, .imm b), (.x4, .ptr (.x26, p.skLen + 1024 * i))])
    (transform (p.skLen + 1024 * i))

def preparePublic (p : Params) : Prog isa :=
  prepareFrame (.seq (copy (.x26, 0) (.x25, 0) p.pkLen)
    (seqR (publicPoly p) 0 p.k))

def prepareSecret (p : Params) : Prog isa :=
  prepareFrame (.seq (copy (.x26, 0) (.x25, 0) p.skLen)
    (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k)))

end VG.Impl.MlDsa.AArch64.PreparedKey

/-! ## The functions, as emitted

`vg_mldsa*_prepare_public_key` and `vg_mldsa*_prepare_secret_key` are their
code above, then their cleanup (`Impl.Residue.AArch64.scrubAll`): the
registers they write that the calling convention does not preserve are
cleared and the 80 bytes of stack they use are zeroed, so that they return
without secret residue. -/

namespace VG.Impl.MlDsa.AArch64.Fn

open VG.Spec.MlDsa (Params)

/-- The registers preparing a verification key writes. -/
def preparePublicClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18], []⟩

/-- The registers preparing a signing key writes. -/
def prepareSecretClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18], []⟩

/-- `vg_mldsa*_prepare_public_key` for the parameter set `p`. -/
def preparePublic (p : Params) : Prog AArch64.isa :=
  Impl.Residue.AArch64.scrubAll 80 0 preparePublicClear (PreparedKey.preparePublic p)

/-- `vg_mldsa*_prepare_secret_key` for the parameter set `p`. -/
def prepareSecret (p : Params) : Prog AArch64.isa :=
  Impl.Residue.AArch64.scrubAll 80 0 prepareSecretClear (PreparedKey.prepareSecret p)

end VG.Impl.MlDsa.AArch64.Fn
