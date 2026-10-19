module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash
import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.Keys
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Spec.TripleDes

/-!
# AES-GCM on x86: `vg_ghash_pclmul`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_pclmul`, from its proof, apart from `Callee.lean`: only the
variants need it, and its proof imports the algebra of
`Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then need not
import.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86

open VG VG.X86

namespace GhashImpl

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86.Pclmul.ghash⟩
  stack := by lit_decide
  ok := Proof.Gcm.X86.Pclmul.ghash_correct
  ct := Proof.Gcm.X86.Pclmul.ghash_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .pclmul => .pclmul

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.gh.impl⟩

end VG.Proof.AesGcm.X86
