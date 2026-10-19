module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytesCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytesCT

/-! # Discharge the primality timing certificates at every supported DSA width -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def PrimeWidths (len drawBytes : Nat) : Prop :=
  (len = 20 ∧ drawBytes = 24) ∨ (len = 32 ∧ drawBytes = 32) ∨
    (len = 128 ∧ drawBytes = 128) ∨ (len = 256 ∧ drawBytes = 256) ∨ (len = 384 ∧ drawBytes = 384)

theorem primeBytes_supported_ct (M : Mont) (K : Kernel) {len drawBytes : Nat}
    (h : PrimeWidths len drawBytes) :
    RelCT isa (Two (PrimeBytesBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run len drawBytes) (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact primeBytes_ct M K _ _ (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
