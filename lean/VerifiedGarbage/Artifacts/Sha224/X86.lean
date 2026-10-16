module

import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sha256.X86.Shared
import Mathlib.Tactic.SplitIfs

/-!
# SHA-224 (FIPS 180-4) on x86 (32-bit)

SHA-224 is SHA-256 from another initial hash value, and its digest the first
28 bytes of the final hash value: its `init` is registered here, its
`update` is SHA-256's (`Artifacts/Sha256/`), and its `finalize`, which
writes its digest, is emitted with each compression function
(`Variants/Sha256/X86/`).
-/

@[expose] public section

namespace VG.Artifacts.Sha224.X86

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := X86.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.X86.Stream.init224
    contract := Spec.Sha256.init224Contract X86.abi
    verified := Proof.Sha256.X86.Shared.init224
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha224.X86
