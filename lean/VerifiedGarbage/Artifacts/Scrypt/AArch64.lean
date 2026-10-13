module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
public import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
public import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
public import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
public import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixCT
public import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
public import VerifiedGarbage.Proof.Scrypt.AArch64.Lit
import Mathlib.Tactic.SplitIfs

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on AArch64
-/

@[expose] public section

namespace VG.Artifacts.Scrypt.AArch64

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := AArch64.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.AArch64.salsa
    contract := Spec.Scrypt.salsaContract AArch64.abi
    verified := Proof.Scrypt.AArch64.salsa_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.blockMixApi with
    target := AArch64.target
    doc := Spec.Scrypt.blockMixApi.doc
    code := Impl.Scrypt.AArch64.blockMix
    contract := Spec.Scrypt.blockMixContract AArch64.abi 16
    stack := 16
    verified := Proof.Scrypt.AArch64.BlockMix.blockMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.roMixApi with
    target := AArch64.target
    doc := Spec.Scrypt.roMixApi.doc
    code := Impl.Scrypt.AArch64.roMix
    contract := Spec.Scrypt.roMixContract AArch64.abi 16
    stack := 16
    verified := Proof.Scrypt.AArch64.RoMix.roMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Scrypt.AArch64
