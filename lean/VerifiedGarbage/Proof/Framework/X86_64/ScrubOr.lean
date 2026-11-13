module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

/-! # Scrubbing where the residue analysis follows the code, else wiping the whole stack -/

/-!
`withScrubOrAll` scrubs an instance of a generic function after its residue
analysis where it has one, and otherwise with every granule of its stack
wiped (`Scrub.withScrubAll`). `withScrubAllM` wipes every granule too, and
clears the vector registers at the level `withScrub` would (`levelFor`):
code that saves, loads and restores MXCSR around the multiplications of
Intel's MCDT list (`mxClass`), but writes no register only AVX-512 has, is
cleared below the level `evex`, and so needs no AVX-512 feature.
-/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

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

/-- `r` with every granule of its stack wiped and the vector registers
cleared at the level `levelFor` of its code, if `scrubRegM`'s side conditions
hold and the clearing needs no CPU feature its code does not; otherwise `r`
itself. -/
def withScrubAllR {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let v := levelFor r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hmx : (mxClass r.code).isSome = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    let r' := scrubRegM r v (allKs (chunks r.stack)) hd hst h8 hlv hmx hrb hpost (resOk_all _ _ h8) hw
      (levelFor_ne _)
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r

/-- `withScrubAllR` where it applies, else `Scrub.withScrubAll`. -/
def withScrubAllM {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let r' := withScrubAllR r hpost
  if r'.residue.isSome then r' else withScrubAll r hpost

end VG.X86_64.RScrub
