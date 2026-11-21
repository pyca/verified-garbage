module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86Comb
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves

/-!
# ECDSA over BrainpoolP384r1 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. `vg_ecdsa_brainpoolp384r1_sign` calls HMAC
through a table: its code is given the functions that the table's calls may
reach (`f`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86.Fn

open VG.X86

/-- `vg_ecdsa_brainpoolp384r1_verify`, as emitted. -/
def verifyBrainpoolP384r1 : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 128
    (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false (Impl.Ecdsa.Verify.X86.verifyBrainpoolP384r1))

/-- `vg_ecdsa_brainpoolp384r1_sign`, as emitted, with `f` the functions its table's calls may reach. -/
def signBrainpoolP384r1 (f : Impl.Ecdsa.Rfc6979.X86.Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 588 (Impl.Ecdsa.Rfc6979.X86.signCode {
    f := f
    w := 2 * Impl.Ecdsa.X86.brainpoolp384r1Comb.n - (if Impl.Ecdsa.X86.brainpoolp384r1Comb.C.len = 28 then 1 else 0)
    len := Impl.Ecdsa.X86.brainpoolp384r1Comb.C.len
    big := false
    sh := 0
    n := Impl.Ecdsa.X86.brainpoolp384r1Comb.C.n
    tries := Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries
    coreN := "vg_ecdsa_brainpoolp384r1_sign_k"
    coreC := Impl.Ecdsa.X86.signBrainpoolP384r1Comb })

end VG.Impl.Ecdsa.X86.Fn
