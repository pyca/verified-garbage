module

public import VerifiedGarbage.Proof.Dsa.X86.MulVerified
public import VerifiedGarbage.Proof.Dsa.X86.MulCall
public import VerifiedGarbage.Proof.Dsa.X86.RedVerified
public import VerifiedGarbage.Proof.Dsa.X86.RedCall
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's reductions and products on baseline i686 -/

@[expose] public section

namespace VG.Artifacts.DsaArith.X86

def reduceHelper (n : Nat)
    (v : Verified X86.target (Impl.Dsa.X86.Arith.reduceBody n)
      (Spec.Dsa.ModArith.reduceContract (Impl.Dsa.X86.Arith.reduceLayout n) X86.abi 20)) : Artifact :=
  (Spec.Dsa.ModArith.reduceApi (Impl.Dsa.X86.Arith.reduceLayout n)).artifact X86.target {
    code := Impl.Dsa.X86.Arith.reduceBody n
    verified := v
    stack := 20
    spSafe := Code.all_of_allInstrs (Proof.Dsa.X86.Red.body_spSafe n) }

def mulHelper (n : Nat)
    (v : Verified X86.target (Impl.Dsa.X86.Arith.mulBody n)
      (Spec.Dsa.ModArith.mulContract (Impl.Dsa.X86.Arith.mulLayout n) X86.abi 20)) : Artifact :=
  (Spec.Dsa.ModArith.mulApi (Impl.Dsa.X86.Arith.mulLayout n)).artifact X86.target {
    code := Impl.Dsa.X86.Arith.mulBody n
    verified := v
    stack := 20
    spSafe := Code.all_of_allInstrs (Proof.Dsa.X86.Mul.body_spSafe n) }

def artifacts : List Artifact := [
  reduceHelper 3 (Proof.Dsa.X86.Red.verified 3),
  reduceHelper 4 (Proof.Dsa.X86.Red.verified 4),
  mulHelper 3 (Proof.Dsa.X86.Mul.verified 3),
  mulHelper 4 (Proof.Dsa.X86.Mul.verified 4),
  mulHelper 16 (Proof.Dsa.X86.Mul.verified 16),
  mulHelper 32 (Proof.Dsa.X86.Mul.verified 32),
  mulHelper 48 (Proof.Dsa.X86.Mul.verified 48)]

end VG.Artifacts.DsaArith.X86
