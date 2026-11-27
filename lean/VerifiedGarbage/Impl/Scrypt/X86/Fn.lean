module

public import VerifiedGarbage.Impl.Scrypt.X86.Scrypt
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# scrypt on x86 (32-bit): the function as emitted

`vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256 named
`pbkName`, followed by its cleanup (`Impl.Scrub.X86.scrubAll 0 116`): the 116
bytes of stack below `esp` that its frame and the functions it calls use
zeroed, and the registers a callee may change cleared, so that it returns
without secret residue. It returns no result.
-/

@[expose] public section

namespace VG.Impl.Scrypt.X86.Fn

open VG.X86

/-- `vg_scrypt`, calling `pbk` named `pbkName`, as emitted. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  -- qualified: inside `Fn`, a bare `scrypt` is `Fn.scrypt` itself
  Impl.Scrub.X86.scrubAll 0 116 (Scrypt.X86.scrypt pbkName pbk)

end VG.Impl.Scrypt.X86.Fn
