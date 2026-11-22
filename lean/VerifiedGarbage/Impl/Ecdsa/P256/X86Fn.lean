module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves

/-!
# ECDSA over P256 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. `vg_ecdsa_p256_sign` calls HMAC
through a table: its code is given the functions that the table's calls may
reach (`f`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86.Fn

open VG.X86

/-- `vg_ecdsa_p256_verify`, as emitted. -/
def verifyP256 : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 128
    (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false (Impl.Ecdsa.Verify.X86.Cfg.verifyComb Impl.Ecdsa.X86.p256Comb))

/-- `vg_ecdsa_p256_sign`, as emitted, with `f` the functions its table's calls may reach. -/
def signP256 (f : Impl.Ecdsa.Rfc6979.X86.Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 612 (Impl.Ecdsa.Rfc6979.X86.signCode {
    f := f
    w := 2 * Impl.Ecdsa.X86.p256Comb.n - (if Impl.Ecdsa.X86.p256Comb.C.len = 28 then 1 else 0)
    len := Impl.Ecdsa.X86.p256Comb.C.len
    big := false
    sh := 0
    n := Impl.Ecdsa.X86.p256Comb.C.n
    tries := Spec.Ecdsa.Rfc6979.Curves.p256.tries
    coreN := "vg_ecdsa_p256_sign_k"
    coreC := Impl.Ecdsa.X86.signP256Comb })

end VG.Impl.Ecdsa.X86.Fn
