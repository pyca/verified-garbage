module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-1 on x86-64 with AVX and BMI: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha1AvxBmi.variant`
(`Variants/MdHash/X86_64/Sha1AvxBmi.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha1AvxBmi

open VG.Impl.Sha1.X86_64.Stream (Callee)

theorem ok : MdStream.X86_64.CalleeOk (P := Proof.Sha1.X86_64.Stream.params) Proof.Sha1.md
    Callee.avxBmi.code :=
  .of_verified Proof.Sha1.X86_64.AvxBmi.compress_verified.1
    Proof.Sha1.X86_64.AvxBmi.compress_verified.2.1
    (by change (instrs Impl.Sha1.X86_64.AvxBmi.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha1.X86_64.AvxBmi.compress.depth = 0; lit_decide)

/-- The compression function with AVX and BMI. -/
def compress : Proof.Sha1.X86_64.Compress where
  callee := .avxBmi
  ok := ok
  mxcsr := by change Impl.Sha1.X86_64.AvxBmi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha1.X86_64.AvxBmi.compress.allInstrs _ = true; lit_decide)
  noStack := by change Impl.Sha1.X86_64.AvxBmi.compress.x86_64Depth = 0; lit_decide
  suffix := "_avx_bmi"
  features := ["avx", "bmi1", "bmi2"]

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha1.variant compress

end VG.Proof.Variants.MdHash.X86_64.Sha1AvxBmi
