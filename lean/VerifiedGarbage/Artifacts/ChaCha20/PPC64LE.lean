module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Shared
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Stream.ApplyCT

/-! # Streaming ChaCha20 (RFC 8439) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.PPC64LE

def artifacts : List Artifact := [
  { Spec.ChaCha20.initApi with
    target := PPC64LE.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.PPC64LE.Stream.init
    contract := Spec.ChaCha20.initContract PPC64LE.abi
    verified := Proof.ChaCha20.PPC64LE.Stream.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.setNonceApi with
    target := PPC64LE.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.PPC64LE.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract PPC64LE.abi
    verified := Proof.ChaCha20.PPC64LE.Stream.setNonce_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.applyApi with
    target := PPC64LE.target
    doc := Spec.ChaCha20.applyApi.doc
    code := Impl.ChaCha20.PPC64LE.Stream.apply
    contract := Spec.ChaCha20.applyContract PPC64LE.abi 0
    verified := Proof.ChaCha20.PPC64LE.Stream.apply_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.PPC64LE
