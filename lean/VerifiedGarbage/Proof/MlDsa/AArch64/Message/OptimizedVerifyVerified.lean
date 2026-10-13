module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyTopTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifySat
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- The ordinary message verifier retains its existing result and public-input
contract while supplying both immutable transform tables to the verified callee. -/
theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p∈params) :
    Verified target (verifyMessage v.callee n c p)
      (verifyMessageContract p (abi.withConsts signRootConsts) 16) :=
  ⟨fun _ h=>let ⟨t,s',he,ha,hq⟩ := verifyMessage_wp v hV hp h; ⟨t,s',he,ha,hq⟩,
    verifyMessage_ct v hV hp,⟨verifySat p,verify_sat (by simpa only [Sign.Ok3,params,List.mem_cons,List.not_mem_nil,or_false] using hp)⟩⟩

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
