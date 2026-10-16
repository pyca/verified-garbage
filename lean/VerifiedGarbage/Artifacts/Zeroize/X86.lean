module

public import VerifiedGarbage.Proof.Zeroize.X86
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86.zeroize
    verified := Proof.Zeroize.X86.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Zeroize.X86
