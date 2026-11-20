module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# What the cleanup of RSA key generation needs of its code (x86, 32-bit)

`vg_rsa_generate` is generic over the implementation of the Miller–Rabin
round it calls, through the prime search and the candidate's test
(`RoundImpl`, `Proof/Variants/MillerRabin/X86.lean`). Its deepest path does
not pass through the round, so its stub gives the round its own budget
(`holeStub 96`, the stack `RoundImpl.stack` bounds) rather than adding it to
the whole (`FillB`, `scrubFSide_of_fillB`): `scrubFSide` of the stub over
the contract's 284 bytes, which the kernel evaluates once (`gen_side`),
holds of the code with every implementation (`gen_scrub`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.GenScrub

open VG.X86 VG.X86.Scrub
open VG.Proof.MillerRabin.X86 (RoundImpl montName montCode)

/-- `vg_rsa_generate` with its Miller–Rabin round a hole of 96 bytes. -/
def genStub : Prog isa :=
  Impl.RsaKeyGen.X86.Generate.code
    (.call "" (Impl.RsaKeyGen.X86.Search.code
      (.call "" (Impl.RsaKeyGen.X86.Candidate.code montName montCode "" (holeStub 96)))))
    Proof.RsaKeyGen.X86.Generate.keyImpl.call

-- The stub as a literal, for the kernel's evaluation.
materialize_code genStub

theorem gen_side : scrubFSide genStub [] 284 = true := by lit_decide

theorem gen_fill (v : RoundImpl) (h : calleeSide v.code 96 = true) :
    FillB genStub (Proof.RsaKeyGen.X86.Generate.genCode v) := by
  unfold genStub
  fillB_calls

/-- `scrubFSide` of `vg_rsa_generate`, whatever the implementation of the
Miller–Rabin round. -/
theorem gen_scrub (v : RoundImpl) : scrubFSide (Proof.RsaKeyGen.X86.Generate.genCode v) [] 284 = true :=
  scrubFSide_of_fillB (gen_fill v (calleeSide_of_le v.stack v.scrub)) gen_side

end VG.Proof.RsaKeyGen.X86.GenScrub
