module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.X86
public import VerifiedGarbage.Impl.Ecdsa.P192.X86Comb
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves

/-!
# ECDSA over P192 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. `vg_ecdsa_p192_sign` calls HMAC
through a table: its code is given the functions that the table's calls may
reach (`f`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86.Fn

open VG.X86

/-- `vg_ecdsa_p192_verify`, as emitted. -/
def verifyP192 : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 128
    (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false (Impl.Ecdsa.Verify.X86.verifyP192))

/-- `vg_ecdsa_p192_sign`, as emitted, with `f` the functions its table's calls may reach. -/
def signP192 (f : Impl.Ecdsa.Rfc6979.X86.Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 612 (Impl.Ecdsa.Rfc6979.X86.signCode {
    f := f
    w := 2 * Impl.Ecdsa.X86.p192Comb.n - (if Impl.Ecdsa.X86.p192Comb.C.len = 28 then 1 else 0)
    len := Impl.Ecdsa.X86.p192Comb.C.len
    big := false
    sh := 0
    n := Impl.Ecdsa.X86.p192Comb.C.n
    tries := Spec.Ecdsa.Rfc6979.Curves.p192.tries
    coreN := "vg_ecdsa_p192_sign_k"
    coreC := Impl.Ecdsa.X86.signP192Comb })

end VG.Impl.Ecdsa.X86.Fn
