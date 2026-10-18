import VerifiedGarbage.Spec.HashFns
import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The streaming functions of the hash functions passed as tables

`HashFns.streaming i` is the hash function `HashId.mgf1 i` names (the same
digest), for 0 to 7 and no other number; its digest is the first bytes of
what its `finalize` writes; and its sizes are those of the hash function's
own `_scratch` functions (`vg_<hash>_update_scratch`,
`vg_<hash>_finalize_scratch`), whose signatures are those of
`HashFns.updateSig` and `HashFns.finalizeSig`, and of its `init`.
-/

namespace VG.Test.HashFns

open VG.Spec

#guard (List.range 16).all fun i => (HashFns.streaming i).isSome == decide (i < 8)

#guard (List.range 8).all fun i => match HashFns.streaming i, HashId.mgf1 i with
  | some T, some H => T.S.digestBytes == H.len && T.S.digestBytes ≤ T.outBytes
  | _, _ => false

example : (HashFns.streaming 0).map (·.S.H.hash) = (HashId.mgf1 0).map (·.hash) := rfl
example : (HashFns.streaming 1).map (·.S.H.hash) = (HashId.mgf1 1).map (·.hash) := rfl
example : (HashFns.streaming 2).map (·.S.H.hash) = (HashId.mgf1 2).map (·.hash) := rfl
example : (HashFns.streaming 3).map (·.S.H.hash) = (HashId.mgf1 3).map (·.hash) := rfl
example : (HashFns.streaming 4).map (·.S.H.hash) = (HashId.mgf1 4).map (·.hash) := rfl
example : (HashFns.streaming 5).map (·.S.H.hash) = (HashId.mgf1 5).map (·.hash) := rfl
example : (HashFns.streaming 6).map (·.S.H.hash) = (HashId.mgf1 6).map (·.hash) := rfl
example : (HashFns.streaming 7).map (·.S.H.hash) = (HashId.mgf1 7).map (·.hash) := rfl

/-- The hash functions' own `init`, `update_scratch` and `finalize_scratch`
signatures, by number. -/
def ownSigs : Nat → Option (Sig × Sig × Sig)
  | 0 => some (Md5.initSig, Md5.updateScratchSig, Md5.finalizeScratchSig)
  | 1 => some (Sha1.initSig, Sha1.updateScratchSig, Sha1.finalizeScratchSig)
  | 2 => some (Sha256.initSig, Sha256.updateScratchSig, Sha256.finalizeScratchSig)
  | 3 => some (Sha256.initSig, Sha256.updateScratchSig, Sha256.finalizeScratchSig)
  | 4 | 5 | 6 | 7 => some (Sha512.initSig, Sha512.updateScratchSig, Sha512.finalizeScratchSig)
  | _ => none

/-- The parameters of a signature, by name and type. -/
def shape (sig : Sig) : List (String × String) :=
  sig.params.map fun (n, p) => (n, match p with
    | .int ty pub => s!"int {repr ty} {pub}"
    | .array w e k => s!"array {w} {e.rust} {k}"
    | .slice w e l => s!"slice {w} {e.rust} {l}"
    | .slices e c => s!"slices {e.rust} {c}")

#guard (List.range 8).all fun i => match HashFns.streaming i, ownSigs i with
  | some T, some (si, su, sf) =>
    shape (HashFns.initSig T) == shape si && shape (HashFns.updateSig T) == shape su &&
      shape (HashFns.finalizeSig T) == shape sf
  | _, _ => false

end VG.Test.HashFns
