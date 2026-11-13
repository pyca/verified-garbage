module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

/-! # Scrubbing where the residue analysis follows the code, else wiping the whole stack -/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64.Scrub

/-- `r` scrubbed after the residue analysis `a` where an instance of a
generic function has one (`withScrub`), and otherwise with every granule of
its stack wiped (`Scrub.withScrubAll`): for the instances whose code the
analysis does not follow, of a function with a small stack. -/
def withScrubOrAll {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | some a => withScrub r hpost pubs hpub (some a)
  | none => withScrubAll r hpost

end VG.X86_64.RScrub
