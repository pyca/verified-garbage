module

public import VerifiedGarbage.Impl.Ed448.X86.PublicKey
public import VerifiedGarbage.Impl.Ed448.X86.SignCached
public import VerifiedGarbage.Impl.Ed448.X86.Verify
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# Ed448 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86.Fn

open VG.X86

/-- `vg_ed448_public_key`, as emitted. -/
def publicKey : Prog isa := Impl.Scrub.X86.scrubAll 0 280 (Impl.Ed448.X86.PublicKey.code Impl.Ed448.X86.scalarBase)

/-- `vg_ed448_sign_cached`, as emitted. -/
def signCached : Prog isa := Impl.Scrub.X86.scrubAll 0 280 (Impl.Ed448.X86.SignCached.code Impl.Ed448.X86.scalarBase)

/-- `vg_ed448_verify`, as emitted. -/
def verify : Prog isa := Impl.Scrub.X86.scrubAll 32 280 (Impl.Ed448.X86.Verify.code Impl.Ed448.X86.verifyEquation)

end VG.Impl.Ed448.X86.Fn
