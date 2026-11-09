module

public import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract

/-! Bounds for the five supported DSA comb layouts, including the padded
2048/160 domain. The retained context never overlaps arithmetic scratch. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG.Impl.Dsa.X86.Comb

/-- Supported modulus-word and exponent-word counts. -/
def Supported (n e : Nat) : Prop :=
  (n = 16 ∧ e = 5) ∨ (n = 32 ∧ e = 5) ∨ (n = 32 ∧ e = 7) ∨
    (n = 32 ∧ e = 8) ∨ (n = 48 ∧ e = 8)

end VG.Proof.Dsa.X86.Comb
