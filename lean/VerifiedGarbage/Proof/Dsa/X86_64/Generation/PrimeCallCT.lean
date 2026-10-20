module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeReturnCT
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeReturnCT
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Native primality calls for exactly the supported DSA parameter sizes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

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

end VG.Proof.Dsa.X86_64.Generation
