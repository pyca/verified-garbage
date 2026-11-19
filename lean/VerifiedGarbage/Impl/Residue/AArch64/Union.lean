module

public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# The registers a function and what it calls write (AArch64)

A function that calls an implementation chosen among several clears, before
returning, the registers its own instructions write and those the
implementation states it writes (`Clear.union`).
-/

@[expose] public section

namespace VG.Impl.Residue.AArch64

/-- The registers of `a` and of `b`, in `Clear.all`'s order: what the tail of
a function clears (`scrubAll`), from the registers its own instructions write
(`a`) and those the implementation it calls states it writes (`b`). -/
def Clear.union (a b : Clear) : Clear where
  gprs := allGprs.filter fun q => a.gprs.contains q || b.gprs.contains q
  vecs := allVecs.filter fun w => a.vecs.contains w || b.vecs.contains w
  his := hiVecs.filter fun w => a.his.contains w || b.his.contains w

end VG.Impl.Residue.AArch64
