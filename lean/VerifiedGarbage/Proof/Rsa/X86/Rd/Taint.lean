module

public import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# `vg_rsa_recover_primes_det` on i686: the taint analysis' registers

The registers the taint analysis takes as public once the working space's
context is set.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 52 }

end VG.Proof.Rsa.X86.Recover
