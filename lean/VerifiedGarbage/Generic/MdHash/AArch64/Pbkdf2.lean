import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# PBKDF2-HMAC (RFC 8018) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate`
(`Impl/Pbkdf2/AArch64.lean`) and the whole `pbkdf2`, the one implementation
for every Merkle–Damgård hash function (`Impl/Pbkdf2/Md/AArch64.lean`),
calling the variant's compression function and the functions made with it, are
emitted once for each variant (`Variants/MdHash/AArch64/`), named with its
suffix.

`stack` is that of the shared contracts: none for `iterate`, which calls
only the compression function (which pushes no frame), and 16 bytes for
`pbkdf2`'s code, whose callees' callees (the streaming functions) may push a
frame saving `x30`. Neither code pushes a frame of its own: each saves its
return address in `scratch`.

`pbkdf2` runs that code in a frame of `8 * pbkdf2Scratch` bytes holding its
working space (`Verified.stackScratch`). For SHA-256, whose `pbkdf2` scrypt's
code calls with its own working space, the code is also emitted on its own,
as `vg_pbkdf2_hmac_sha256_scratch`.
-/

namespace VG.Generic.MdHash.AArch64.Pbkdf2

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  { v.I.iterateApi with
    name := v.I.iterateApi.name ++ v.suffix
    target := AArch64.target
    doc := v.I.iterateApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := v.H.iterate
    contract := v.I.iterateContract AArch64.abi
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    verified := v.iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { v.I.pbkdf2Api with
    name := v.I.pbkdf2Api.name ++ v.suffix
    target := AArch64.target
    doc := v.I.pbkdf2Api.doc
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I) .x7 v.H.pbkdf2
    contract := v.I.pbkdf2Contract AArch64.abi (16 + Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I
    verified := v.pbkdf2F
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }] ++
  -- Scrypt's code calls `pbkdf2` of SHA-256 with its own working space.
  match v.sha256 with
  | none => []
  | some _ => [
    { v.I.pbkdf2ScratchApi with
      name := v.I.pbkdf2ScratchApi.name ++ v.suffix
      target := AArch64.target
      doc := v.I.pbkdf2ScratchApi.doc
      code := v.H.pbkdf2
      contract := v.I.pbkdf2ScratchContract AArch64.abi 16
      ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2ScratchContract; rfl⟩
      stack := 16
      verified := v.pbkdf2
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := v.features }]

end VG.Generic.MdHash.AArch64.Pbkdf2
