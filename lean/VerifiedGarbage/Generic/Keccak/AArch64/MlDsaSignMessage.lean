module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Message

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSignMessage
open VG VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.PreparedKey
open VG.Proof.MlDsa.AArch64.Sign

def entry (v : Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p)
    (module label : String) (prepared : Bool) : Artifact :=
  (if prepared then preparedSignMessageApi p module label else signMessageApi p module label).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := pairedSignRootConsts
    code := Impl.MlDsa.AArch64.Message.signMessage v.callee
      ((if prepared then preparedSignApi p module label else signApi p module label).name ++ v.callee.suffix)
      (signCode v p ((signWithCacheApi p module label).name ++ v.callee.suffix) prepared) p
    stack := 64
    verified := message_sign_verified v hp (message_sign_fn v hp _ prepared)
    ofSig := by cases prepared <;> of_sig
    ofApi := by cases prepared <;> rfl }

def entries (v : Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p)
    (module label : String) : List Artifact := [entry v p hp module label false,entry v p hp module label true]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  entries v mlDsa44 (.inl rfl) "mldsa44" "ML-DSA-44" ++
  entries v mlDsa65 (.inr (.inl rfl)) "mldsa65" "ML-DSA-65" ++
  entries v mlDsa87 (.inr (.inr rfl)) "mldsa87" "ML-DSA-87"

end VG.Generic.Keccak.AArch64.MlDsaSignMessage
