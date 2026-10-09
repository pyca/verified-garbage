import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified

namespace VG.Proof.MlDsa.AArch64.Message.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (pairedSignRootConsts)

/-- Cached commitments preserve the existing message-wrapper callee contract
and its sixteen-byte stack bound. -/
theorem signFn_of_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65∨p=mlDsa87)
    (hv : Verified target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) 16)) :
    Paired.SignFn p (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  ⟨hv,cachedPairedSignWith_dle v hp⟩

/-- The cached signer is wrapped by the existing verified message/context
handling, retaining the original public contract and rejection behavior. -/
theorem signMessage_of_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65∨p=mlDsa87) (n : String)
    (hv : Verified target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) 16)) :
    Verified target (signMessage v.callee n
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) p)
      (signMessageContract p (abi.withConsts pairedSignRootConsts) 16) := by
  apply Paired.signMessage_verified v (signFn_of_verified v hp hv)
  rcases hp with rfl|rfl
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem signFn (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    Paired.SignFn p (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  signFn_of_verified v hp (Sign.Cached.sign_verified v hp)

theorem signMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65∨p=mlDsa87) (n : String) :
    Verified target (signMessage v.callee n
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) p)
      (signMessageContract p (abi.withConsts pairedSignRootConsts) 16) :=
  signMessage_of_verified v hp n (Sign.Cached.sign_verified v hp)

end VG.Proof.MlDsa.AArch64.Message.Cached
