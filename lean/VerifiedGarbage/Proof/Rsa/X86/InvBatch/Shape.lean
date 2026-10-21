module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic

/-! # Stack-pointer safety of each batched inversion kernel -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare
 theorem body64_noSp : (Impl.Rsa.X86.InvBatch.body 64 32).allInstrs noSp=true := by rsa_stack_shape
 theorem body96_noSp : (Impl.Rsa.X86.InvBatch.body 96 48).allInstrs noSp=true := by rsa_stack_shape
 theorem body128_noSp : (Impl.Rsa.X86.InvBatch.body 128 64).allInstrs noSp=true := by rsa_stack_shape
end VG.Proof.Rsa.X86.InvBatch
