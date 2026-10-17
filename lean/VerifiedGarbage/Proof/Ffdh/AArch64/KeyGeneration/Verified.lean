module

public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.CT
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Implies
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase

/-! # The verified key search (AArch64)

For any attempt that uses no stack of its own (`key_verified`), and for
the one `Artifacts/Ffdh/AArch64.lean` registers: `vg_ffdh_generate_key` with
the five-bit window helper, the vector table selection and the baseline
Montgomery multiplication (`baseAttempt`, `key_verified_base`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem key_verified (a : Attempt) :
    Verified target (Impl.Ffdh.AArch64.KeyGeneration.Search.code a.call)
      (Spec.Ffdh.keySearchContract abi stackUse) :=
  Verified.of_correct (key_correct a) (key_constantTime a) key_implies

/-- The registered `vg_ffdh_generate_key`, which has no frames. -/
def baseAttempt : Attempt :=
  ⟨WindowFive.called, Mont.base, WindowVector.selector, by decide +kernel⟩

/-- The key search calling it. -/
abbrev keyCode : Prog isa := Impl.Ffdh.AArch64.KeyGeneration.Search.code baseAttempt.call

theorem key_verified_base : Verified target keyCode (Spec.Ffdh.keySearchContract abi stackUse) :=
  key_verified baseAttempt

end VG.Proof.Ffdh.AArch64.KeyGeneration
