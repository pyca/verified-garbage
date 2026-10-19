module

/-! # The combined arithmetic check for RSA CRT parameters -/

@[expose] public section
namespace VG.Proof.Rsa.CrtValues

def maskOf (P Q X₁ X₂ V : Nat) : Bool := P % 2 = 1 ∧ X₁ = Q ∧ X₂ = 0 ∧ V = 1

end VG.Proof.Rsa.CrtValues
