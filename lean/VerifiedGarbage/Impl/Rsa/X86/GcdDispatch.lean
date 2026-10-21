module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt -- shake: keep (argOp occurs in exposed program definitions)

/-! # Public-width selection for prime recovery's GCD -/

@[expose] public section
namespace VG.Impl.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Rsa.X86.KeyRt

def choice (len : Nat) : List Instr :=
 [.mov .eax (.mem (argOp 5)),.alu .cmp .eax (.imm (BitVec.ofNat 32 len))]

def choose (len words : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block (choice len)) (.ite .e (body words) fallback)

def dispatch (fallback : Prog isa) : Prog isa :=
 choose 256 66 (choose 384 98 (choose 512 130 fallback))

end VG.Impl.Rsa.X86.GcdBatch
