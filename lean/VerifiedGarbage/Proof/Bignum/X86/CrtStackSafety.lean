module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-! # Instructions that keep the stack pointer, for compositional stack-pointer safety -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

def stackSafe (i : Instr) : Bool := !isa.writesSp i

end VG.Proof.Bignum.X86.Crt
