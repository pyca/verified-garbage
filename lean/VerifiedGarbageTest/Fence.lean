import VerifiedGarbage.Proof.Framework.X86_64.Fence
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
import VerifiedGarbage.TCB.Axioms

/-!
# Fencing real artifacts

`X86_64.verified_fence` applies to every verified x86-64 artifact, whether
its constant time was proven by the taint analysis (X25519) or by relating
two runs, `RelCT` (FFDH's key generation), and depends on the standard
axioms only.
-/

namespace VG.Test.Fence

open VG.X86_64

theorem x25519_fenced [Proof.X25519.X86_64.DivstepInv] {S : Spectre isa}
    (hf : S.fence .lfence = true) :
    let c := Impl.X25519.X86_64.x25519.fenceFn .lfence
    let k := Spec.X25519.x25519Contract abi 8
    Verified target c k ∧ SpecConstantTime S k.pre k.pub c :=
  verified_fence Proof.X25519.X86_64.x25519_verified hf

theorem ffdh_init_fenced {S : Spectre isa} (hf : S.fence .lfence = true) :
    let c := Impl.Ffdh.X86_64.Generation.init.fenceFn .lfence
    let k := Spec.Ffdh.parameterInitContract abi
    Verified target c k ∧ SpecConstantTime S k.pre k.pub c :=
  verified_fence Proof.Ffdh.X86_64.Generation.init_verified hf

#assert_standard_axioms verified_fence
#assert_standard_axioms x25519_fenced
#assert_standard_axioms ffdh_init_fenced

end VG.Test.Fence
