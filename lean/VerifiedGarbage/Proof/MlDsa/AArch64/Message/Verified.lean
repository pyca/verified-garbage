import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.DepthVerify
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: verified

Untrusted: everything here is checked by Lean. `signMessage v.callee n c p`
and `verifyMessage v.callee n c p`, for any functions on `μ` `c` they can
call (`SignFn`, `VerifyFn`), are verified against `signMessageContract p
AArch64.abi 16` and `verifyMessageContract p AArch64.abi 16`; the functions
on `μ` with the Keccak permutation of `v` are such functions (`signFn`,
`verifyFn`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition of verification. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageContract p AArch64.abi 16).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
      List.range.loop] [verifySat] using verifySat mlDsa87

theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified AArch64.target (verifyMessage v.callee n c p) (verifyMessageContract p AArch64.abi 16) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp v hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct v hV hp, verifyMessage_sat hp⟩

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p ∈ params) :
    VerifyFn p (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  refine ⟨?_, verifyWith_dle v p⟩
  rcases params3 hp with rfl | rfl | rfl
  · exact Verify.verify44_verifiedWith (keccak := v)
  · exact Verify.verify65_verifiedWith (keccak := v)
  · exact Verify.verify87_verifiedWith (keccak := v)

end VG.Proof.MlDsa.AArch64.Message
