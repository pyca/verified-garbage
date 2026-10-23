module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic

/-! # Stack-pointer safety of each batched inversion kernel -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare
 theorem body64_noSp : (Impl.Rsa.X86.InvBatch.body 64 32).allInstrs noSp=true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Rsa.X86.InvBatch.body, Impl.Rsa.X86.InvBatch.seqs,
    Impl.Rsa.X86.Keys.seqs, instrs,
    Impl.Rsa.X86.InvBatch.init, Impl.Rsa.X86.InvBatch.operands,
    Impl.Rsa.X86.InvBatch.coefficients, Impl.Rsa.X86.InvBatch.inverseSetup,
    Impl.Rsa.X86.InvBatch.update, Impl.Rsa.X86.InvBatch.normalize,
    Impl.Rsa.X86.InvBatch.twice, Impl.Rsa.X86.InvBatch.finish,
    Impl.Rsa.X86.InvBatch.absolute, List.all_append]
  decide +kernel
 theorem body96_noSp : (Impl.Rsa.X86.InvBatch.body 96 48).allInstrs noSp=true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Rsa.X86.InvBatch.body, Impl.Rsa.X86.InvBatch.seqs,
    Impl.Rsa.X86.Keys.seqs, instrs,
    Impl.Rsa.X86.InvBatch.init, Impl.Rsa.X86.InvBatch.operands,
    Impl.Rsa.X86.InvBatch.coefficients, Impl.Rsa.X86.InvBatch.inverseSetup,
    Impl.Rsa.X86.InvBatch.update, Impl.Rsa.X86.InvBatch.normalize,
    Impl.Rsa.X86.InvBatch.twice, Impl.Rsa.X86.InvBatch.finish,
    Impl.Rsa.X86.InvBatch.absolute, List.all_append]
  decide +kernel
 theorem body128_noSp : (Impl.Rsa.X86.InvBatch.body 128 64).allInstrs noSp=true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Rsa.X86.InvBatch.body, Impl.Rsa.X86.InvBatch.seqs,
    Impl.Rsa.X86.Keys.seqs, instrs,
    Impl.Rsa.X86.InvBatch.init, Impl.Rsa.X86.InvBatch.operands,
    Impl.Rsa.X86.InvBatch.coefficients, Impl.Rsa.X86.InvBatch.inverseSetup,
    Impl.Rsa.X86.InvBatch.update, Impl.Rsa.X86.InvBatch.normalize,
    Impl.Rsa.X86.InvBatch.twice, Impl.Rsa.X86.InvBatch.finish,
    Impl.Rsa.X86.InvBatch.absolute, List.all_append]
  decide +kernel
end VG.Proof.Rsa.X86.InvBatch
