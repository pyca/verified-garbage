module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.DomainFacts
public import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Every checked API domain supplies the native comb's arithmetic geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Proof.Bignum

def checkedParameters (B src ctx : Addr) (Z k : Nat) (dom : List Byte)
 (room : slot ((k+7)/8) 8≤Z) (small : 64≤k) (large : k≤1024)
 (valid : Spec.Ffdh.domainValid k dom=true) : Parameters := by
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 exact {
  B:=B,Z:=Z,w:=(k+7)/8,mi:=0,P:=(Spec.Ffdh.domainOf k dom).p,G:=(Spec.Ffdh.domainOf k dom).g,
  N:=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom),k:=k,src:=src,ctx:=ctx,
  table:=ctx+BitVec.ofNat 64 (24+16*((k+7)/8)),room:=room,positive:=by omega,width:=by omega,
  modulusPositive:=by omega,coprime:=coprime_pow2 modulus.1.1.1 (64*((k+7)/8)) }

end VG.Proof.Ffdh.AArch64.Cached
