module

public import VerifiedGarbage.Proof.Rsa.X86.RtShape
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

/-! # `vg_rsa_private_precompute` on x86: the stack its code uses

`primes` uses no stack below its entry's `esp`, `vg_rsa_public_precompute`
96 bytes, and neither writes `esp` (`primes_stack`, `primes_noSp`, `pc_stack`,
`pc_noSp`); and the function, with them, writes no `esp` but by its frames
(`code_spSafe`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare
open VG.Impl.Bignum.X86.PrivPre (primes code)

theorem primes_stack : stackUse primes = 0 := by rsa_stack_use

theorem primes_all : primes.allInstrs noSp = true := by rsa_stack_shape

theorem primes_noSp : NoSp primes := NoSp.of_all primes_all

theorem pc_stack : stackUse Impl.Bignum.X86.PrecomputeFn.code = 96 := by rsa_stack_use

theorem pc_all : Impl.Bignum.X86.PrecomputeFn.code.allInstrs noSp = true := by rsa_stack_shape

theorem pc_noSp : NoSp Impl.Bignum.X86.PrecomputeFn.code := NoSp.of_all pc_all

theorem code_spSafe :
    (code "vg_rsa_public_precompute" Impl.Bignum.X86.PrecomputeFn.code "vg_rsa_private_precompute_primes"
      primes).all (fun i => !isa.writesSp i) = true :=
  Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

end VG.Proof.Bignum.X86.PrivPre
