module

public import VerifiedGarbage.Spec.Aes

/-! # AES key-expansion round constants -/

@[expose] public section
namespace VG.Impl.Aes.KeyWords

def rc (j : Nat) : BitVec 8 := Nat.repeat Spec.Aes.xtimes (j-1) 1

end VG.Impl.Aes.KeyWords
