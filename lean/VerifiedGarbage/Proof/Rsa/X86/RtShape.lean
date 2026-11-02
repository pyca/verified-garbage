module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedRt
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

/-! # Stack-pointer safety of RSA callers, reusing the Montgomery proof -/

@[expose] public section
namespace VG.Proof.Rsa.X86.RtShape
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare

 theorem recover_all : Impl.Rsa.X86.RecoverRt.code.allInstrs noSp=true := by
  rsa_stack_shape

 theorem recoverDet_all : Impl.Rsa.X86.RecoverDetRt.code.allInstrs noSp=true := by
  rsa_stack_shape

 theorem privateCrt_all : (Impl.Bignum.X86.CrtRt.code).allInstrs noSp=true := by
  rsa_stack_shape

 theorem precomputed_all : (Impl.Bignum.X86.PrecomputedRt.code).allInstrs noSp=true := by
  rsa_stack_shape

 theorem public_all : (Impl.Bignum.X86.PublicRt.code).allInstrs noSp=true := by
  rsa_stack_shape

 theorem crtValues_all : (Impl.Rsa.X86.CrtValuesRt.code).allInstrs noSp=true := by
  rsa_stack_shape

 theorem check_all (full : Bool) : (Impl.Rsa.X86.KeyCheckRt.code full).allInstrs noSp=true := by
  cases full <;> rsa_stack_shape

 theorem all_spSafe {c : Prog isa} (h : c.allInstrs noSp=true) : c.all (fun i => !isa.writesSp i)=true := by
  have e : (fun i : Instr => !isa.writesSp i)=noSp := by funext i; cases i <;> rfl
  rw [e]
  exact Code.all_of_allInstrs h

 theorem recover_spSafe : (Impl.Rsa.X86.RecoverRt.code).all (fun i => !isa.writesSp i)=true := all_spSafe recover_all

 theorem recoverDet_spSafe : (Impl.Rsa.X86.RecoverDetRt.code).all (fun i => !isa.writesSp i)=true :=
  all_spSafe recoverDet_all

 theorem privateCrt_spSafe : (Impl.Bignum.X86.CrtRt.code).all (fun i => !isa.writesSp i)=true := all_spSafe privateCrt_all

 theorem precomputed_spSafe : (Impl.Bignum.X86.PrecomputedRt.code).all (fun i => !isa.writesSp i)=true := all_spSafe precomputed_all

 theorem public_spSafe : (Impl.Bignum.X86.PublicRt.code).all (fun i => !isa.writesSp i)=true := all_spSafe public_all

 theorem crtValues_spSafe : (Impl.Rsa.X86.CrtValuesRt.code).all (fun i => !isa.writesSp i)=true := all_spSafe crtValues_all

 theorem check_spSafe (full : Bool) : (Impl.Rsa.X86.KeyCheckRt.code full).all (fun i => !isa.writesSp i)=true := all_spSafe (check_all full)

 theorem privateCrt_stack : stackUse (Impl.Bignum.X86.CrtRt.code)=96 := by
  rsa_stack_use

 theorem precomputed_stack : stackUse (Impl.Bignum.X86.PrecomputedRt.code)=96 := by
  rsa_stack_use

 theorem public_stack : stackUse (Impl.Bignum.X86.PublicRt.code)=96 := by
  rsa_stack_use

 theorem recover_stack : stackUse (Impl.Rsa.X86.RecoverRt.code)=96 := by
  rsa_stack_use

end VG.Proof.Rsa.X86.RtShape
