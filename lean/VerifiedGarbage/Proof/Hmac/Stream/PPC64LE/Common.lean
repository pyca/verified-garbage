module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.Framework.Offset

/-!
# HMAC over any streaming hash function on PPC64LE: shared lemmas

What survives the writes of the code and of the functions it calls: a
streaming state representing whole blocks, whose hash value nothing wrote
(`HashOK.repr_keep`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- A streaming state representing whole blocks survives writes outside its
hash value. -/
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {x : List Byte}
    (hx : x.length % H.B = 0) (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) (hr : hH.SH.Repr m p x) :
    hH.SH.Repr m' p x :=
  hH.reloc m m' p p x hx (fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have : H.N ≤ 64 := hH.dims.N.2; show H.N ≤ 2 ^ 64; omega) hi) hr

end HashOK

end VG.Proof.Hmac.Stream.PPC64LE
