module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

/-!
# Streaming functions that return without secret residue (x86-64)

`StreamFn.scrub`: a streaming function (`StreamFn`) followed by
`Impl.Scrub.X86_64.scrubTail`, which clears the registers and the granules
`ks` of its stack that the residue analysis finds may hold secrets
(`RScrub.resOk_reg`), verified against the same contract
(`X86_64.Scrub.Verified.scrub`) and without secret residue
(`StreamFn.scrub_noResidue`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- The bits of the result of `f`'s function. -/
abbrev StreamFn.retBits (f : StreamFn) : Nat :=
  f.api.sig.retBits ((abi.withConsts f.reg.consts).withTables f.api.sig f.reg.tables).ptrBits

/-- `f`, scrubbed at level `v`, wiping the granules `ks` of its stack. -/
def StreamFn.scrub (f : StreamFn) (v : VecLevel) (ks : List Nat)
    (hd : f.code.x86_64Depth ≤ f.stack) (hst : f.stack + 8 < 2 ^ 64) (h8 : f.stack % 8 = 0)
    (hlv : f.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : f.retBits ≤ 32 ∨ f.retBits = 64) (hpost : PostOut f.contract f.retBits)
    (hres : ResOk f.code f.contract f.stack ks (chunks f.stack)) : StreamFn where
  api := f.api
  code := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl).code
  contract := f.contract
  stack := f.stack
  verified := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl).verified
  ofSig := f.ofSig
  ofApi := f.ofApi
  spSafe := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl).spSafe

theorem StreamFn.scrub_noResidue (f : StreamFn) (v : VecLevel) (ks : List Nat)
    (hd : f.code.x86_64Depth ≤ f.stack) (hst : f.stack + 8 < 2 ^ 64) (h8 : f.stack % 8 = 0)
    (hlv : f.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : f.retBits ≤ 32 ∨ f.retBits = 64) (hpost : PostOut f.contract f.retBits)
    (hres : ResOk f.code f.contract f.stack ks (chunks f.stack)) :
    NoResidue (f.scrub v ks hd hst h8 hlv hrb hpost hres).code f.contract f.retBits :=
  scrubReg_noResidue f.reg v ks hd hst h8 hlv hrb hpost hres rfl

end VG.Proof.Pbkdf2.Md.X86_64
