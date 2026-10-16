module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Lit

/-!
# SHA-256 on x86-64: the scalar compression function: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha256.variant`
(`Variants/MdHash/X86_64/Sha256.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256

/-- The scalar compression function. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .scalar
  ok := Proof.Sha256.X86_64.Stream.scalar_ok
  mxcsr := by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha256.variant compress

end VG.Proof.Variants.MdHash.X86_64.Sha256
