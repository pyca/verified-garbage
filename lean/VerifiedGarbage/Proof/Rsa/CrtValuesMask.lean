module

/-! # The combined arithmetic check for RSA CRT parameters -/

@[expose] public section
namespace VG.Proof.Rsa.CrtValues

def maskOf (P Q X₁ X₂ V : Nat) : Bool := P % 2 = 1 ∧ X₁ = Q ∧ X₂ = 0 ∧ V = 1

/-- The same check, `p q = n` by the product. -/
def maskOfP (P Q N V : Nat) : Bool := P % 2 = 1 ∧ P * Q = N ∧ V = 1

end VG.Proof.Rsa.CrtValues
