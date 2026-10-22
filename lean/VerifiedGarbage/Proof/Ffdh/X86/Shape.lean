module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Rsa.X86.RtShape

/-! # FFDH on i686: no instruction writes `esp` -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Shape

open VG VG.X86 VG.Proof.Mont.X86.StaticSquare

theorem checkDomain_spSafe : (Impl.Ffdh.X86.CheckDomain.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

end VG.Proof.Ffdh.X86.Shape
