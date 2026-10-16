module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackEnd
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-DSA (FIPS 204) on x86: the encodings

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.X86

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.simpleBitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.SimpleBitPack.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.bitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.bitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.BitPack.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.bitUnpackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.bitUnpack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.BU.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.unpackT1Api.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.unpackT1
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.T1.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.hintBitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.hintBitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Hint.hintBitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.hintBitUnpackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.hintBitUnpack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Hint.hintBitUnpack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaPack.X86
