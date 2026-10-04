import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7

The code uses 8 bytes of stack: it pushes the two stack arguments of
`vg_poly1305_finalize_scratch` around its call; its calls (`bl`) keep the
return address in `lr`, which it saves in its working space. Each function
keeps its working space (632 bytes, `work`) in a frame of 656 bytes on the
stack (`withStackScratchWiped`, which also copies the three other stack
arguments), zeroed after the code, as it holds the one-time Poly1305 key and
keystream.
-/

namespace VG.Artifacts.ChaCha20Poly1305.Arm

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := Arm.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract Arm.abi 664
    stack := 664
    verified := Proof.ChaCha20Poly1305.Arm.seal_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20Poly1305.openApi with
    target := Arm.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«open»
    contract := Spec.ChaCha20Poly1305.openContract Arm.abi 664
    stack := 664
    verified := Proof.ChaCha20Poly1305.Arm.open_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20Poly1305.Arm
