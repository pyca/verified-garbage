module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-256 on x86-64 with the SHA extensions: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha256ShaNi.variant`
(`Variants/MdHash/X86_64/Sha256ShaNi.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256ShaNi

/-- The compression function with the SHA extensions. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .shani
  ok := Proof.Sha256.X86_64.Stream.shani_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_shani"
  features := ["sha", "ssse3"]
  -- `scratch` holds only the round constants (`Impl.Sha256.X86_64.ShaNi`).
  wipe := 0

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha256.variant compress

end VG.Proof.Variants.MdHash.X86_64.Sha256ShaNi
