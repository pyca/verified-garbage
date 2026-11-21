module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86
public import VerifiedGarbage.Impl.Ecdsa.P521.X86Comb
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves

/-!
# ECDSA over P521 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. `vg_ecdsa_p521_sign` calls HMAC
through a table: its code is given the functions that the table's calls may
reach (`f`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86.Fn

open VG.X86

/-- `vg_ecdsa_p521_verify`, as emitted. -/
def verifyP521 : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 128
    (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true (Impl.Ecdsa.Verify.X86.verifyP521))

/-- `vg_ecdsa_p521_sign`, as emitted, with `f` the functions its table's calls may reach. -/
def signP521 (f : Impl.Ecdsa.Rfc6979.X86.Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 588 (Impl.Ecdsa.Rfc6979.X86.signCode {
    f := f
    w := 2 * Impl.Ecdsa.X86.p521Comb.n - (if Impl.Ecdsa.X86.p521Comb.C.len = 28 then 1 else 0)
    len := Impl.Ecdsa.X86.p521Comb.C.len
    big := true
    sh := 7
    n := Impl.Ecdsa.X86.p521Comb.C.n
    tries := Spec.Ecdsa.Rfc6979.Curves.p521.tries
    coreN := "vg_ecdsa_p521_sign_k"
    coreC := Impl.Ecdsa.X86.signP521Comb })

end VG.Impl.Ecdsa.X86.Fn
