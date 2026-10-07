import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified

/-!
# The checked RSA private-key operation on AArch64

A generic file (see `TCB/Emit.lean`): `vg_rsa_private_checked`, calling an
implementation `v` of `vg_rsa_private_crt` and the public operation it
comes with, is emitted once for each implementation
(`Variants/RsaPrivateCrt/AArch64/`), named with its suffix, and needs its
CPU features.

It uses 3248 bytes of stack: a 16-byte frame saving `x30` and one of 3232
bytes, which holds the CRT's result, the precomputed values of `n`, the
arguments kept across the calls and the stack arguments of the calls,
whose callees use no stack.
-/

namespace VG.Generic.RsaPrivateCrt.AArch64.Rsa

open VG.Proof.Rsa.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  { Spec.Rsa.privateCheckedApi with
    name := privName v
    target := AArch64.target
    doc := Spec.Rsa.privateCheckedApi.doc (notes := ["This implementation computes the result `m` with `" ++
      v.name ++ "` into its frame, then `m^e mod n` with `" ++ v.pcName ++ "` and `" ++ v.pdName ++
      "`, which also checks `e`. It compares that with the input in constant time, and copies `m` to `out` \
      under a mask, which is clear unless the CRT and the public operation succeeded and the two match. \
      The result, 1, 2 or 0, is computed from the mask without a branch. Then it overwrites the frame's \
      copy of `m` with zeros."])
    code := privCode v
    contract := Spec.Rsa.privateCheckedContract AArch64.abi stackBytes
    stack := stackBytes
    verified := code_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.RsaPrivateCrt.AArch64.Rsa
