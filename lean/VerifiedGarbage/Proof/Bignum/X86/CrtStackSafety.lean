module

public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa
public import Init.Prelude
public import VerifiedGarbage.TCB.Code

/-! # Instructions that keep the stack pointer, for compositional stack-pointer safety -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

def stackSafe (i : Instr) : Bool := !isa.writesSp i

end VG.Proof.Bignum.X86.Crt
