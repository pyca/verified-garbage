import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece

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

/-- The encryption loop named `n`, for a key context of
`vg_aes_gcm_init_precomputed`: those that read the powers of the hash subkey
from it, or the others. -/
def encP : StitchName → Prog isa
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZP.enc
  | n => n.enc

/-- The decryption loop named `n`, for a key context of
`vg_aes_gcm_init_precomputed`. -/
def decP : StitchName → Prog isa
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZP.dec
  | n => n.dec

/-- Whether `seal` and `open` calling the loops named `n` take the short path
for short inputs (`GcmImpl.short`): the loops on 512-bit registers, whose
CPU features it needs. -/
def short : StitchName → Bool
  | .vaesAvx512 => true
  | _ => false

end StitchName

/-- The facts `Piece` states of the loops named `n` for a key context of
`vg_aes_gcm_init_precomputed`. -/
structure PieceP (n : StitchName) : Type where
  enc : Piece n.encP
  dec : Piece n.decP

/-- Interleaved loops that encrypt out of place, for
`vg_aes_gcm_encrypt_blocks_to`, by name. `StitchToName.ok`, in the generic
file, gives their proof. -/
inductive StitchToName where
  /-- `Impl.Gcm.X86_64.StitchZTo`: VAES and VPCLMULQDQ on 512-bit registers. -/
  | vaesAvx512

namespace StitchToName

/-- The loop named `n`. -/
def enc : StitchToName → Prog isa
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZTo.enc

/-- The loop named `n`, for a key context of `vg_aes_gcm_init_precomputed`. -/
def encP : StitchToName → Prog isa
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZTo.encP

end StitchToName

/-- The facts `PieceTo` states of the loop named `n` for a key context of
`vg_aes_gcm_init_precomputed`. -/
structure PieceToP (n : StitchToName) : Type where
  enc : PieceTo n.encP

/-- Out-of-place loops by name, with the facts `PieceTo` states of them (and
of those for a key context of `vg_aes_gcm_init_precomputed`, if they read
the powers of the hash subkey from it). -/
structure StitchToPart where
  name : StitchToName
  piece : PieceTo name.enc
  pieceP : Option (PieceToP name) := none

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
  /-- The same, of the loops for a key context of
  `vg_aes_gcm_init_precomputed`, for the loops that read the powers of the
  hash subkey from it (`none`: the `_precomputed` functions are not built
  for this variant). -/
  pieceP : Option (PieceP name) := none
  /-- The loops that encrypt out of place for `vg_aes_gcm_encrypt_blocks_to`,
  with the same CPU features (`none`: it copies the blocks to the output and
  encrypts them there). -/
  toPart : Option StitchToPart := none

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
