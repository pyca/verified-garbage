module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeReturnCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeReturnCT

/-! # Native primality calls for exactly the supported DSA parameter sizes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

def PrimeCallShape (w candidate len draw checks : Nat) : Prop :=
  (w = 4 ∧ candidate = q ∧ len = 20 ∧ draw = 24 ∧ checks = 64) ∨
  (w = 4 ∧ candidate = q ∧ len = 32 ∧ draw = 32 ∧ checks = 64) ∨
  (w = 16 ∧ candidate = p ∧ len = 128 ∧ draw = 128 ∧ checks = 64) ∨
  (w = 32 ∧ candidate = p ∧ len = 256 ∧ draw = 256 ∧ checks = 64) ∨
  (w = 48 ∧ candidate = p ∧ len = 384 ∧ draw = 384 ∧ checks = 128)

theorem primeCall_ct (M : Mont) (K : Kernel) {w candidate len draw checks : Nat}
    (h : PrimeCallShape w candidate len draw checks) :
    RelCT isa (Two (CheckPrimeBefore w candidate len draw checks))
      (.seq (checkPrime M.mm K.run w candidate len draw checks) (.block primeResult)) (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  all_goals exact checkPrimeReturn_ct M K _ _ _ _ _ (by unfold PrimeWidths; decide +kernel) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
