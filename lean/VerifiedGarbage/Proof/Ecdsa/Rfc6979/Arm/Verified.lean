module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hashes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: `Verified`

For a curve `R`, with the hash functions `hsArm`: a run's `hash` is one of
`hashIds` (the precondition), which names one of them (`hashOf`); for it,
`sign_ok` gives the contract's postcondition and keeps the callee-saved
registers and the stack pointer (`abiPreserved`), and `sign_ct` constant
time up to the number of candidates, for runs whose `hash`, which is public,
agrees. Each curve's file shows that its contract implies `rfcArm`
(`sign_verified`'s `himp`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm

variable (R : RfcCurve)

/-- The number `hash` is one of `hashIds`. -/
theorem hash_mem {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcArm I 456).pre s) :
    (stackArg s 1).toNat ∈ Spec.Ecdsa.Rfc6979.hashIds := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ := h
  exact hm

theorem sign_arm (s : State) (h : (rfcArm R.I 456).pre s) :
    ∃ t s', Exec isa (cfgR R hsArm).sign s t s' ∧ abiPreserved s s' ∧ (rfcArm R.I 456).post s s' := by
  obtain ⟨P, rfl, hs, hk⟩ := hashOf R (hash_mem h)
  rw [← hs]
  exact sign_ok (P := P) h hk.symm

theorem sign_ct_any : ConstantTime isa (rfcArm R.I 456).pre (rfcArm R.I 456).pub (cfgR R hsArm).sign := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨P, rfl, hs, hk⟩ := hashOf R (hash_mem h₁)
  rw [← hs] at e₁ e₂
  have hk₂ : (stackArg s₂ 1).toNat = P.k := by rw [← hp.2.2.2.2.2.2.1]; exact hk.symm
  exact sign_ct _ _ _ _ _ _ ⟨h₁, hk.symm⟩ ⟨h₂, hk₂⟩ hp e₁ e₂

/-- The notes on the implementation, for the documentation of the function,
for scalars of `q` bytes signed by `core`, and whether they are longer than
every hash's output (`wide`, with an order of `nb` bits). -/
def signNotes (q : Nat) (wide : Bool) (nb : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` " ++
  (if wide then "as the digest's integer, below `n`, in " ++ toString q ++ " bytes"
    else "by a conditional subtraction of `n` from the digest's leftmost " ++ toString q ++ " bytes") ++
  ", and each HMAC with HMAC's `init`, the streaming `update` and HMAC's `finalize` of the hash \
  function `hash` names, chosen by comparing `digest_len + (hash + 4) / 8` (its output length, plus \
  one if its block is 128 bytes) with each one's, using the start of `scratch` for HMAC's states and \
  working space and the message. Each candidate `k`, the leftmost " ++ toString nb ++ " bits of as \
  many successive `V`s as they take, is tried with `" ++ core ++ "`, which uses all of `scratch`" ++
  (if wide then ", with the digest's leftmost bits shifted into " ++ toString q ++ " bytes" else "") ++
  "; whether to try another is computed without branches from its result and the count of candidates \
  left, so the code branches only on that and on the hash function. `K`, `V`, `h`, the candidate, \
  `core`'s digest and our caller's registers are kept in a 432-byte frame, whose secrets are cleared \
  before it is freed; the calls use the 24 bytes below it."

theorem sign_verified (himp : (rfcArm R.I 456).Implies (R.I.signAnyContract Arm.abi 456)) :
    Verified Arm.target (cfgR R hsArm).sign (R.I.signAnyContract Arm.abi 456) :=
  Verified.of_correct (sign_arm R) (sign_ct_any R) himp

end VG.Proof.Ecdsa.Rfc6979.Arm
