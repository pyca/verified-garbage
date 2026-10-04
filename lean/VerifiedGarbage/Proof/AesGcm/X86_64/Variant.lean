import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx

/-!
# AES-GCM on x86-64: the variants

Untrusted: everything here is checked by Lean. What a variant of `AesGcm`
is (see `TCB/Emit.lean`): the implementations its functions call, with the
proofs that import the algebra of `Proof/Gcm/Poly.lean` (those of
`vg_ghash` and of the interleaved loops) named rather than held, so that the
variants need not import that algebra. The generic file
(`Generic/AesGcm/X86_64/AesGcm.lean`) resolves the names (`GcmVariant.impl`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The interleaved loops for `vg_aes_gcm_encrypt_blocks` and
`_decrypt_blocks`, by name. `StitchName.ok`, in the generic file, gives
their proof. -/
inductive StitchName where
  /-- `Impl.Gcm.X86_64.Stitch`: VAES and VPCLMULQDQ on 256-bit registers. -/
  | vaes
  /-- `Impl.Gcm.X86_64.StitchZ`: VAES and VPCLMULQDQ on 512-bit registers. -/
  | vaesAvx512
  /-- `Impl.Gcm.X86_64.StitchAvx`: AES-NI and PCLMULQDQ in `VEX.128`. -/
  | aesniAvx

namespace StitchName

/-- The encryption loop named `n`. -/
def enc : StitchName → Prog isa
  | .vaes => Impl.Gcm.X86_64.Stitch.enc
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZ.enc
  | .aesniAvx => Impl.Gcm.X86_64.StitchAvx.enc

/-- The decryption loop named `n`. -/
def dec : StitchName → Prog isa
  | .vaes => Impl.Gcm.X86_64.Stitch.dec
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZ.dec
  | .aesniAvx => Impl.Gcm.X86_64.StitchAvx.dec

end StitchName

/-- A `StitchImpl` with its loops named, and so without their proof of
`StitchOk` (`StitchName.ok`). -/
structure StitchPart where
  name : StitchName
  /-- What the names of the instances using them end with, after the
  callees' suffixes. -/
  suffix : String
  /-- The CPU features they need beyond the callees'. -/
  features : List String
  encP : Piece name.enc
  decP : Piece name.dec

/-- A variant of `AesGcm` (see `TCB/Emit.lean`): a `GcmImpl` with its
implementation of `vg_ghash` (`GhashName`) and its interleaved loops
(`StitchPart`) named, which `GcmVariant.impl`, in the generic file,
resolves. -/
structure GcmVariant where
  ctr : Ctr32Impl
  key : KeyImpl
  gh : GhashName
  stitch : Option StitchPart := none

end VG.Proof.AesGcm.X86_64
