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

theorem sign_ppc (P : Rfc) {N : Nat} (hN : 400 + Impl.Ecdsa.Rfc6979.PPC64LE.extra P.c.hHigh = N) (s : State)
    (h : (rfcPPC P.I N).pre s) :
    ∃ t s', Exec isa P.c.sign s t s' ∧ abiPreserved s s' ∧ (rfcPPC P.I N).post s s' := by
  subst hN; exact sign_ok h

theorem sign_verified (P : Rfc) (B : Blks P.K P.c) {N : Nat}
    (hN : 400 + Impl.Ecdsa.Rfc6979.PPC64LE.extra P.c.hHigh = N)
    (himp : (rfcPPC P.I N).Implies (P.I.signContract PPC64LE.abi N)) :
    Verified PPC64LE.target P.c.sign (P.I.signContract PPC64LE.abi N) := by
  subst hN; exact Verified.of_correct (sign_ppc P rfl) (sign_ct B) himp

/-- The notes on the implementation, for the documentation of the function
with HMAC's functions `hi`, `upd` and `hf`, for scalars of `q` bytes signed
by `core`, with `h` at the frame's top if `hHigh`. -/
def signNotes (hi upd hf : String) (q : Nat) (core : String) (hHigh : Bool := false) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost " ++
  toString q ++ " bytes, a 32-bit digit at a time, and each HMAC with `" ++ hi ++ "`, `" ++ upd ++ "` and `" ++
  hf ++ "`, using the start of `scratch` for HMAC's states and working space and the message. Each candidate \
  `k`, the leftmost " ++ toString q ++ " bytes of `V`, is tried with `" ++ core ++ "`, which uses all of \
  `scratch`; whether to try another is computed without branches from its result and the count of candidates \
  left, so the code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a " ++
  (if hHigh then "320-byte stack frame (`h` in its top 64 bytes)" else "256-byte stack frame") ++
  " below the 48-byte frame saving the link register, and the secrets are cleared before it is \
  freed; the calls use the 96 bytes below it."

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
