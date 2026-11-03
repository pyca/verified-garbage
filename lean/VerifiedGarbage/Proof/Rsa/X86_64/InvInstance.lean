module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Main

/-! # The batched inverse's contract on x86-64, supplied at the registrations

`InvLaw`, proved in `InvB/Main.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

instance invLaw : InvLaw where
  inverseN_ok := InvB.inverseN_ok
  inverse_ok := InvB.inverse_ok

end VG.Proof.Rsa.X86_64
