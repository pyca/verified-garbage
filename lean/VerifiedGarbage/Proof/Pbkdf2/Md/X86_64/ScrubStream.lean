module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry

-- separate module: generic over the hash functions, of which SHA-256 is the first to use it

/-!
# Streaming functions that return without secret residue (x86-64)

`StreamFn.scrub`: a streaming function (`StreamFn`) followed by
`Impl.Scrub.X86_64.scrubTail`, which clears the registers and the granules
`ks` of its stack that the residue analysis finds may hold secrets
(`RScrub.resOk_reg`), verified against the same contract
(`X86_64.Scrub.Verified.scrub`) and without secret residue
(`StreamFn.scrub_noResidue`).

`MdHash.hmacFinReg`: HMAC's `finalize` over a variant, followed by
`scrubTail` where the variant gives the residue analysis of its code
(`MdHash.hmacFinRes`). Its postcondition reads the memory on return only
within `out` (`hmacFinOut`).

`scrubAllCode`: code followed by the clearing with every granule of its stack
wiped, as `Scrub.scrubRegAll` does of a registered function, for code that
is part of one (`scrubAllCode_ok`).

`InitImpl`: an implementation of HMAC's `init` for a key of any length, as a
registration file states it. `MdHash.init` is a variant's, and
`MdHash.initScrubbed` the same with the clearing after each of its two
branches, every granule of the branch's own frame wiped (`initCodeS`),
which returns without secret residue: no residue analysis is needed, and
one clearing after both would wipe the larger frame of the branch for long
keys for every key. The frame of the branch for a key of at most a block
holds only the working space its code uses (`initFrame`), so that is all
it wipes. `MdHash.initAuto` checks `initScrubbed`'s side conditions when the
emitter runs, at the lowest level that covers the code.
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
    (hres : ResOk f.code f.contract f.stack ks (chunks f.stack)) (hne : v ≠ .evex := by decide) : StreamFn where
  api := f.api
  code := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl hne).code
  contract := f.contract
  stack := f.stack
  verified := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl hne).verified
  ofSig := f.ofSig
  ofApi := f.ofApi
  spSafe := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl hne).spSafe
  residue := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl hne).residue

theorem StreamFn.scrub_noResidue (f : StreamFn) (v : VecLevel) (ks : List Nat)
    (hd : f.code.x86_64Depth ≤ f.stack) (hst : f.stack + 8 < 2 ^ 64) (h8 : f.stack % 8 = 0)
    (hlv : f.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : f.retBits ≤ 32 ∨ f.retBits = 64) (hpost : PostOut f.contract f.retBits)
    (hres : ResOk f.code f.contract f.stack ks (chunks f.stack)) (hne : v ≠ .evex := by decide) :
    NoResidue (f.scrub v ks hd hst h8 hlv hrb hpost hres hne).code f.contract f.retBits :=
  scrubReg_noResidue f.reg v ks hd hst h8 hlv hrb hpost hres rfl hne

/-- HMAC's `finalize`'s postcondition reads the memory on return only within
`out`, the HMAC's bytes. -/
theorem hmacFinOut (I : Spec.Hmac.Instance) (hD : I.S.digestBytes < 2 ^ 64) (stack : Nat) :
    PostOut (I.finalizeContract abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨inn, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨otr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Hmac.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < I.S.digestBytes, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega) (by omega))).symm
    intro k0 text h1 h2 hri hc hro
    show Spec.Sha256.bytesAt m₂ out I.S.digestBytes = _
    rw [Sha256.Stream.bytesAt_congr ho]
    exact h k0 text h1 h2 hri hc hro

open RScrub in
/-- HMAC's `finalize` over the variant `v`: `finalize_scratch` with its
working space in a frame of its own, without secret residue where `v` gives
its analysis (`MdHash.hmacFinRes`). -/
def MdHash.hmacFinReg (v : MdHash) : Registration v.I.finalizeApi target :=
  let r : Registration v.I.finalizeApi target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch (hmacFrame v.I) .r8 v.H.hmacFin
    stack := 16 + hmacFrame v.I
    verified := v.hmacFinF
    spSafe := X86_64.withStackScratch_spSafe_of v.hmacFinSp }
  if hD : v.I.S.digestBytes < 2 ^ 64 then
    withScrub r (hmacFinOut v.I hD _) [] (pubOk_nil _) v.hmacFinRes
  else r

/-- `c` followed by the clearing (`scrub`) at the level `v`, with every granule
of its `stack` bytes of stack wiped: for code that is part of a function (a
branch of it, verified against a contract of its own). -/
def scrubAllCode (v : VecLevel) (rb stack : Nat) (c : Prog isa) : Prog isa :=
  scrub v rb (xsOf c (allKs (chunks stack))) (psOf (allKs (chunks stack))) (gsOf Taint.clobbers c)
    (allKs (chunks stack)) (chunks stack) c

/-- `scrubAllCode` is verified against the contract of its code, and returns
without secret residue, below the level `evex`. -/
theorem scrubAllCode_ok {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {v : VecLevel}
    (hne : v ≠ .evex) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack) (hst : stack + 8 < 2 ^ 64)
    (h8 : stack % 8 = 0) (hlv : c.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :
    Verified target (scrubAllCode v (sig.retBits A.ptrBits) stack c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (scrubAllCode v (sig.retBits A.ptrBits) stack c) (sig.contract A pre post wa stack leak)
        (sig.retBits A.ptrBits) :=
  have he := evexReg_of_ne (c := c) (ks := allKs (chunks stack)) (stack := stack) hne
  Verified.scrub hA h (SpSafe.of_all hsp) hd (chunks_sum stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb hpost (resOk_all _ _ h8) (tailOk_of _ _ _)
    (xs_of _ _) he.1 he.2 (gs_of _ _)

theorem scrubAllCode_spSafe (v : VecLevel) (rb stack : Nat) {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubAllCode v rb stack c).all (fun i => !isa.writesSp i) = true :=
  scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 c (allKs (chunks stack))).psOk
    (tailOk_of 0 c (allKs (chunks stack))).gsOk h

/-- HMAC's `init`'s postcondition reads the memory on return only within
its two states, for a key of at most a block and of any length. -/
theorem hmacInitOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

theorem hmacInitAnyOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- `initCode`, each of its two branches followed by the clearing at the
level `lv`, with every granule of the branch's frame wiped. -/
def initCodeS (lv : VecLevel) (Ho H : Impl.Pbkdf2.Md.X86_64.Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize
    (scrubAllCode lv ((Spec.Hmac.initSig I.S).retBits 64) (16 + initFrame Ho)
      (Impl.StackScratch.X86_64.withStackScratch (initFrame Ho) .r8 Ho.hmacInit))
    (scrubAllCode lv ((Spec.Hmac.initSig I.S).retBits 64) (24 + anyFrame I)
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny))

/-- `initCodeS` is verified, and returns without secret residue, if `scrub`'s
side conditions hold of its two branches. -/
theorem initCodeS_ok (v : MdHash) {lv : VecLevel} (hne : lv ≠ .evex) (hS : v.I.S.stateBytes < 2 ^ 64)
    (hd₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).x86_64Depth ≤
      16 + initFrame v.Ho)
    (hd₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).x86_64Depth ≤ 24 + anyFrame v.I)
    (hst : 24 + anyFrame v.I + 8 < 2 ^ 64) (hn : 16 + initFrame v.Ho ≤ 24 + anyFrame v.I)
    (h8₁ : (16 + initFrame v.Ho) % 8 = 0) (h8₂ : (24 + anyFrame v.I) % 8 = 0)
    (hl₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).all
      (fun i => decide (i.vecLevel ≤ lv.level)) = true)
    (hl₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).all (fun i => decide (i.vecLevel ≤ lv.level)) = true)
    (hrb : (Spec.Hmac.initSig v.I.S).retBits 64 ≤ 32 ∨ (Spec.Hmac.initSig v.I.S).retBits 64 = 64) :
    Verified target (initCodeS lv v.Ho v.H v.I) (v.I.initAnyKeyContract abi (24 + anyFrame v.I)) ∧
      NoResidue (initCodeS lv v.Ho v.H v.I) (v.I.initAnyKeyContract abi (24 + anyFrame v.I))
        ((Spec.Hmac.initSig v.I.S).retBits 64) := by
  have s := scrubAllCode_ok (A := abi) ScrubAbi.plain (sig := Spec.Hmac.initSig v.I.S)
    (pre := Spec.Hmac.initPre v.I.S abi.ptrBits) (post := Spec.Hmac.initPost v.I.S abi.ptrBits) (wa := true)
    (leak := none) hne v.hmacShortF v.hmacShortFSp hd₁ (by omega) h8₁ hl₁ hrb (hmacInitOut v.I v.reprLocal hS _)
  have l := scrubAllCode_ok (A := abi) ScrubAbi.plain (sig := Spec.Hmac.initSig v.I.S)
    (post := Spec.Hmac.initPost v.I.S abi.ptrBits) (wa := true)
    (leak := none) hne v.hmacAnyF v.hmacAnyFSp hd₂ hst h8₂ hl₂ hrb (hmacInitAnyOut v.I v.reprLocal hS _)
  exact ⟨initEntry_verified s.1 l.1 (by omega) hn v.hBlock v.hmacInitF.2.2,
    initEntry_noResidue s.2 l.2 (by omega) hn v.hBlock⟩

theorem initCodeS_spSafe (v : MdHash) (lv : VecLevel) :
    (initCodeS lv v.Ho v.H v.I).all (fun i => !isa.writesSp i) = true := by
  simp only [initCodeS, Impl.Pbkdf2.Md.X86_64.initEntry, Code.iteCold, Code.all,
    scrubAllCode_spSafe lv _ _ v.hmacShortFSp, scrubAllCode_spSafe lv _ _ v.hmacAnyFSp, Bool.and_true]
  rfl

/-- An implementation of HMAC's `init` for a key of any length, of instance
`I` (`vg_hmac_<hash>_init`): what its registration states. -/
structure InitImpl (I : Spec.Hmac.Instance) where
  /-- What follows the function's name. -/
  suffix : String
  /-- CPU features it is chosen only with, beyond those its code needs
  (`Registration.extra`): for an `init` that is faster only on some of the
  CPUs that can run it, which a feature its code does not use tells apart. -/
  extra : List String := []
  code : Prog isa
  verified : Verified target code (I.initAnyKeyContract abi (24 + anyFrame I))
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- That it returns without secret residue, if it does. -/
  residue : Option (PLift (NoResidue code (I.initAnyKeyContract abi (24 + anyFrame I))
    ((Spec.Hmac.initSig I.S).retBits 64))) := none

/-- HMAC's `init` over the variant `v`: `initCode`. -/
def MdHash.init (v : MdHash) : InitImpl v.I where
  suffix := v.suffix
  code := initCode v.Ho v.H v.I
  verified := v.hmacInitF
  spSafe := v.hmacInitFSp

/-- HMAC's `init` over the variant `v`, with the clearing after each of its
two branches (`initCodeS`) at the level `lv`, chosen only with the features
`extra` too: it returns without secret residue. -/
def MdHash.initScrubbed (v : MdHash) (lv : VecLevel) (extra : List String) (hne : lv ≠ .evex)
    (hS : v.I.S.stateBytes < 2 ^ 64)
    (hd₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).x86_64Depth ≤
      16 + initFrame v.Ho)
    (hd₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).x86_64Depth ≤ 24 + anyFrame v.I)
    (hst : 24 + anyFrame v.I + 8 < 2 ^ 64) (hn : 16 + initFrame v.Ho ≤ 24 + anyFrame v.I)
    (h8₁ : (16 + initFrame v.Ho) % 8 = 0) (h8₂ : (24 + anyFrame v.I) % 8 = 0)
    (hl₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).all
      (fun i => decide (i.vecLevel ≤ lv.level)) = true)
    (hl₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).all (fun i => decide (i.vecLevel ≤ lv.level)) = true)
    (hrb : (Spec.Hmac.initSig v.I.S).retBits 64 ≤ 32 ∨ (Spec.Hmac.initSig v.I.S).retBits 64 = 64) :
    InitImpl v.I where
  suffix := v.suffix
  extra := extra
  code := initCodeS lv v.Ho v.H v.I
  verified := (initCodeS_ok v hne hS hd₁ hd₂ hst hn h8₁ h8₂ hl₁ hl₂ hrb).1
  spSafe := initCodeS_spSafe v lv
  residue := some ⟨(initCodeS_ok v hne hS hd₁ hd₂ hst hn h8₁ h8₂ hl₁ hl₂ hrb).2⟩

/-- HMAC's `init` over the variant `v`, chosen only with the features `extra`
too: `MdHash.initScrubbed` at the lowest level that covers its code
(`levelAll`), if `scrub`'s side conditions hold and the clearing needs no CPU
feature its code does not; otherwise `MdHash.init`, which the emitter
refuses unless `ci/residue_allowlist.txt` lists it. -/
def MdHash.initAuto (v : MdHash) (extra : List String := []) : InitImpl v.I :=
  let r : InitImpl v.I := { v.init with extra := extra }
  let lv := levelAll (initCode v.Ho v.H v.I)
  if hne : lv ≠ .evex then
  if hS : v.I.S.stateBytes < 2 ^ 64 then
  if hd₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).x86_64Depth ≤
      16 + initFrame v.Ho then
  if hd₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).x86_64Depth ≤ 24 + anyFrame v.I then
  if hst : 24 + anyFrame v.I + 8 < 2 ^ 64 then
  if hn : 16 + initFrame v.Ho ≤ 24 + anyFrame v.I then
  if h8₁ : (16 + initFrame v.Ho) % 8 = 0 then
  if h8₂ : (24 + anyFrame v.I) % 8 = 0 then
  if hl₁ : (Impl.StackScratch.X86_64.withStackScratch (initFrame v.Ho) .r8 v.Ho.hmacInit).all
      (fun i => decide (i.vecLevel ≤ lv.level)) = true then
  if hl₂ : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.I) .r8 v.I.initAnyKeyScratch
      v.H.hmacInitAny).all (fun i => decide (i.vecLevel ≤ lv.level)) = true then
  if hrb : (Spec.Hmac.initSig v.I.S).retBits 64 ≤ 32 ∨ (Spec.Hmac.initSig v.I.S).retBits 64 = 64 then
    let r' := v.initScrubbed lv extra hne hS hd₁ hd₂ hst hn h8₁ h8₂ hl₁ hl₂ hrb
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r else r else r else r else r

end VG.Proof.Pbkdf2.Md.X86_64
