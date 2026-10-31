module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on PPC64LE: `Verified`

From the correctness of the whole function (`sign_ok`) and its constant time
(`sign_ct`), for an instance whose shared contract implies `rfcPPC`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

theorem sign_ppc (P : Rfc) {N : Nat} (hN : 400 + Impl.Ecdsa.Rfc6979.PPC64LE.extra P.c.hHigh P.c.wide = N) (s : State)
    (h : (rfcPPC P.I N).pre s) :
    ∃ t s', Exec isa P.c.sign s t s' ∧ abiPreserved s s' ∧ (rfcPPC P.I N).post s s' := by
  subst hN; exact sign_ok h

theorem sign_verified (P : Rfc) (B : Blks P.K P.c) {N : Nat}
    (hN : 400 + Impl.Ecdsa.Rfc6979.PPC64LE.extra P.c.hHigh P.c.wide = N)
    (himp : (rfcPPC P.I N).Implies (P.I.signContract PPC64LE.abi N)) :
    Verified PPC64LE.target P.c.sign (P.I.signContract PPC64LE.abi N) := by
  subst hN; exact Verified.of_correct (sign_ppc P rfl) (sign_ct B) himp

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
