import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT

/-!
# Deterministic ECDSA on 32-bit ARM: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the stack pointer (`abiPreserved`), and
`sign_ct` constant time up to the number of candidates. Each instance's file
shows that its contract implies `rfcArm` (`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm

variable (P : RfcHash)

theorem sign_arm (s : State) (h : (rfcArm P.I).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcArm P.I).post s s' :=
  sign_ok (P := P) h

/-- The notes on the implementation, for the documentation of the function
with HMAC's `init` `hiN`, the streaming `update` `updN` and HMAC's
`finalize` `hfN`, for scalars of `q` bytes signed by `core`. -/
def signNotes (hiN updN hfN : String) (q : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost " ++
  toString q ++ " bytes, and each HMAC with `" ++ hiN ++ "`, `" ++ updN ++ "` and `" ++ hfN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost " ++ toString q ++ " bytes of `V`, is tried with `" ++ core ++ "`, which uses all of \
  `scratch`; whether to try another is computed without branches from its result and the count of \
  candidates left, so the code branches only on that. `K`, `V`, `h` and our caller's registers are kept \
  in a 216-byte frame, whose secrets are cleared before it is freed; the calls use the 24 bytes below it."

theorem sign_verified (himp : (rfcArm P.I).Implies (P.I.signContract Arm.abi 240)) :
    Verified Arm.target (cfgOf P).sign (P.I.signContract Arm.abi 240) :=
  Verified.of_correct (sign_arm P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.Arm
