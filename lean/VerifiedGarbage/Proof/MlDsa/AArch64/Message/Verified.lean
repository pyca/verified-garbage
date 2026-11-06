module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message_cached`: the functions on `μ`

Untrusted: everything here is checked by Lean. `vg_mldsa*_verify`, with the
Keccak permutation of `v`, is a function that `verify_message_cached` can
call (`verifyFn`); `signSat` satisfies the precondition of signing.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition of signing. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x4000 | .x7 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

/-! ## The functions on `μ` -/

theorem params3 {p : Params} (hp : p ∈ params) : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87 := by
  simpa only [params, List.mem_cons, List.not_mem_nil, or_false] using hp

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p ∈ params) :
    VerifyFn p (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  refine ⟨?_, verifyWith_dle v p⟩
  rcases params3 hp with rfl | rfl | rfl
  · exact Verify.verify44_verifiedWith (keccak := v)
  · exact Verify.verify65_verifiedWith (keccak := v)
  · exact Verify.verify87_verifiedWith (keccak := v)

end VG.Proof.MlDsa.AArch64.Message
