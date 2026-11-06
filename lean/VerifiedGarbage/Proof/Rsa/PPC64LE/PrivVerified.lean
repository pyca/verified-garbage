module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked` on PPC64LE: the shared contract on the registers

`fnContract` states the shared contract's postcondition on the registers and
the stack.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Proof.Rsa.privateCheckedContract abi frameBytes).pre
  post := fnPost
  pub := (Proof.Rsa.privateCheckedContract abi frameBytes).pub

end VG.Proof.Rsa.PPC64LE.Priv
