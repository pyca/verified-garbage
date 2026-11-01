module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.Satisfiable
public import Init.Prelude
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct

/-! The private comb helper satisfies the merged DSA shared-context contract. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem private_verified {n e : Nat} (h : Supported n e) :
    Verified target (body false n e) (Proof.Dsa.FixedBaseComb.powerContract (layout n e) abi 20) :=
  ⟨correct h false,private_constantTime h,satisfiable h false⟩

end VG.Proof.Dsa.X86.Comb
