module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import Init.Prelude
public import VerifiedGarbage.TCB.X86.Target

/-! # Shared key-generation contract on the native cdecl ABI

The code saves sixteen bytes of registers. Native arithmetic helpers also
carry a twenty-byte stack separation condition, so the contract reserves
their conservative gap even though key assembly makes no nested calls.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def keyStack : Nat := 36
def contract : Contract isa := Spec.RsaKeyGen.keyContract abi keyStack

end VG.Proof.RsaKeyGen.X86.Key
