module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import Init.Prelude
public import VerifiedGarbage.TCB.X86.Target

/-! # Shared key-generation contract on the native cdecl ABI

The code saves sixteen bytes of registers. Below them it calls
`vg_rsa_keygen_inverse` with twelve bytes of arguments, whose contract keeps
36 bytes below its return address apart from its buffers: 68 bytes in all.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def keyStack : Nat := 68
def contract : Contract isa := Spec.RsaKeyGen.keyContract abi keyStack

end VG.Proof.RsaKeyGen.X86.Key
