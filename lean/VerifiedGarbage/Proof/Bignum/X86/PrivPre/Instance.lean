module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Shape
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified

/-! # `vg_rsa_private_precompute` on x86: the code and its proof

With `vg_rsa_public_precompute` and `primes` (emitted as the internal
function `vg_rsa_private_precompute_primes`) as its callees.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86

def ppCode : Prog isa :=
  Impl.Bignum.X86.PrivPre.code "vg_rsa_public_precompute" Impl.Bignum.X86.PrecomputeFn.code
    "vg_rsa_private_precompute_primes" Impl.Bignum.X86.PrivPre.primes

theorem pp_verified : Verified target ppCode (Spec.Rsa.privatePrecomputeContract abi stackBytes) :=
  verified precompute_verified (by rw [pc_stack]) pc_noSp (by rw [primes_stack]; decide) primes_noSp

theorem pp_spSafe : ppCode.all (fun i => !isa.writesSp i) = true := code_spSafe

end VG.Proof.Bignum.X86.PrivPre
