module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Poly1305 (RFC 8439 §2.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Poly1305.PPC64LE

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.init
    verified := Proof.Poly1305.PPC64LE.Shared.init },
  Spec.Poly1305.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 Impl.Poly1305.PPC64LE.update
    stack := 160
    verified := Proof.Poly1305.PPC64LE.Shared.update },
  Spec.Poly1305.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.finalize
    stack := 160
    verified := Proof.Poly1305.PPC64LE.Shared.finalize }]

end VG.Artifacts.Poly1305.PPC64LE
