module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SHA-224 (FIPS 180-4) on RISC-V

SHA-224 is SHA-256 from another initial hash value, and its digest the first
28 bytes of the final hash value: its `init` and `finalize` are registered
here, and its `update` is SHA-256's (`Artifacts/Sha256/`). `finalize` keeps
its working space in a frame of its own, as SHA-256's does.
-/

@[expose] public section

namespace VG.Artifacts.Sha224.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.init224
    verified := Proof.Sha256.RISCV64.Shared.init224 },
  Spec.Sha256.finalize224Api.artifact RISCV64.target {
    notes := ["Keeps its working space, and the registers it saves, in a frame of 144 bytes on the \
        stack."]
    code := Impl.Sha256.RISCV64.Stream.finalize224
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.finalize224 }]

end VG.Artifacts.Sha224.RISCV64
