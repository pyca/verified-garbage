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

`FinImpl`: HMAC's `finalize` over a variant, followed by its cleanup, with
what the cleanup needs of its code, which the variant evaluates. Its postcondition reads the memory on return only
within `out` (`hmacFinOut`).

`InitImpl`: an implementation of HMAC's `init` for a key of any length, as a
registration file binds it. `MdHash.initSel` is a variant's, with the
cleanup after each of its two branches, every granule of the branch's own
frame wiped (`initCodeA`): no residue analysis is needed, and one cleanup
after both would wipe the larger frame of the branch for long keys for
every key. The frame of the branch for a key of at most a block holds only
the working space its code uses (`initFrame`), so that is all it wipes.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

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
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hD, hi]))).symm
    intro k0 text h1 h2 hri hc hro
    show Spec.Sha256.bytesAt m₂ out I.S.digestBytes = _
    rw [Sha256.Stream.bytesAt_congr ho]
    exact h k0 text h1 h2 hri hc hro

/-- HMAC's `finalize` over the variant `v`: `finalize_scratch` with its
working space in a frame of its own (`MdHash.hmacFinF`), with what its
cleanup (`Impl.Scrub.X86_64.scrubSel`) needs of its code (`sel`), which the
variant evaluates once, where it is defined. -/
structure FinImpl where
  v : MdHash
  hD : v.I.S.digestBytes < 2 ^ 64 := by decide
  sel : SelScrub v.I.finalizeApi.sig (16 + hmacFrame v.H) ((Spec.Hmac.finalizeSig v.I.S).retBits 64)
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame v.H) .r8 v.H.hmacFin)

/-- `f`'s function before its cleanup. -/
def FinImpl.plain (f : FinImpl) : Unscrubbed f.v.I.finalizeApi target where
  suffix := f.v.suffix
  code := Impl.StackScratch.X86_64.withStackScratch (hmacFrame f.v.H) .r8 f.v.H.hmacFin
  stack := 16 + hmacFrame f.v.H
  verified := f.v.hmacFinF
  spSafe := X86_64.withStackScratch_spSafe_of f.v.hmacFinSp

/-- `f`'s code as emitted, its code and then its cleanup, meets its contract
in constant time and returns without secret residue. -/
theorem FinImpl.scrubbed (f : FinImpl) :
    VerifiedScrubbed target
      (scrubSel f.sel.level ((Spec.Hmac.finalizeSig f.v.I.S).retBits 64) (16 + hmacFrame f.v.H) f.sel.runs
        f.plain.code)
      f.plain.contract ((Spec.Hmac.finalizeSig f.v.I.S).retBits 64) :=
  SelScrub.scrubbed f.plain f.sel (hmacFinOut f.v.I f.hD _)

/-- `f` as a registration of its `Api` (`Api.artifact`): its code as emitted,
with its cleanup, and the theorem about that code (`FinImpl.scrubbed`). -/
def FinImpl.reg (f : FinImpl) : Registration f.v.I.finalizeApi target where
  suffix := f.v.suffix
  consts := []
  tables := []
  code := scrubSel f.sel.level ((Spec.Hmac.finalizeSig f.v.I.S).retBits 64) (16 + hmacFrame f.v.H) f.sel.runs
    f.plain.code
  contract := f.plain.contract
  stack := f.plain.stack
  verified := .scrubbed f.scrubbed
  ofApi := f.plain.ofApi
  ofSig := f.plain.ofSig
  spSafe := scrubKs_spSafe f.plain.spSafe

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

/-- HMAC's `init` for a key of at most a block (`initCode`'s first branch),
as an `Api` of its own: the branch is verified against a contract of its own
(`MdHash.hmacShortF`), and this is what its proof states it of. It is never
registered. -/
def shortApi (I : Spec.Hmac.Instance) : Api :=
  { I.initAnyKeyApi with contracts := some fun A stack => I.initContract A stack }

/-- `initCode`'s branch for a key of at most a block, before its cleanup. -/
def MdHash.shortPlain (v : MdHash) : Unscrubbed (shortApi v.I) target where
  code := Impl.StackScratch.X86_64.withStackScratch (initFrame v.H) .r8 v.H.hmacInit
  contract := v.I.initContract abi (16 + initFrame v.H)
  stack := 16 + initFrame v.H
  verified := v.hmacShortF
  spSafe := v.hmacShortFSp

/-- `initCode`'s branch for a longer key, before its cleanup. -/
def MdHash.anyPlain (v : MdHash) : Unscrubbed v.I.initAnyKeyApi target where
  code := Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.H) .r8 (anyWords v.H) v.H.hmacInitAny
  stack := 24 + anyFrame v.H
  verified := v.hmacAnyF
  spSafe := v.hmacAnyFSp

/-- `initCode`, each of its two branches followed by its cleanup at the level
`lv`, with every granule of the branch's own frame wiped
(`Impl.Scrub.X86_64.scrubAll`): no residue analysis is needed, and one
cleanup after both would wipe the larger frame of the branch for long keys
for every key. -/
def initCodeA (lv : VecLevel) (H : Impl.Pbkdf2.Md.X86_64.Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize
    (scrubAll lv ((Spec.Hmac.initSig I.S).retBits 64) (16 + initFrame H)
      (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit))
    (scrubAll lv ((Spec.Hmac.initSig I.S).retBits 64) (24 + anyFrame H)
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H) H.hmacInitAny))

/-- `initCodeA` meets the contract of `vg_hmac_<hash>_init` in constant time
and returns without secret residue, given what the cleanup of each branch
needs of its code (`h₁`, `h₂`, by `lit_decide`). -/
theorem initCodeA_scrubbed (v : MdHash) (lv : VecLevel) (hS : v.I.S.stateBytes < 2 ^ 64)
    (hn : 16 + initFrame v.H ≤ 24 + anyFrame v.H)
    (h₁ : scrubSideG v.shortPlain.code (16 + initFrame v.H) ((Spec.Hmac.initSig v.I.S).retBits 64) lv true
      (wipeKs (chunksA (16 + initFrame v.H))) (chunksA (16 + initFrame v.H))
      (gsAll (wipeKs (chunksA (16 + initFrame v.H)))) [] = true)
    (h₂ : scrubSideG v.anyPlain.code (24 + anyFrame v.H) ((Spec.Hmac.initSig v.I.S).retBits 64) lv true
      (wipeKs (chunksA (24 + anyFrame v.H))) (chunksA (24 + anyFrame v.H))
      (gsAll (wipeKs (chunksA (24 + anyFrame v.H)))) [] = true) :
    VerifiedScrubbed target (initCodeA lv v.H v.I) (v.I.initAnyKeyContract abi (24 + anyFrame v.H))
      ((Spec.Hmac.initSig v.I.S).retBits 64) :=
  have s := verifiedScrubbedAll v.shortPlain lv (hmacInitOut v.I v.reprLocal hS _) h₁
  have l := verifiedScrubbedAll v.anyPlain lv (hmacInitAnyOut v.I v.reprLocal hS _) h₂
  ⟨initEntry_verified s.verified l.verified (by omega_using []) hn v.hBlock v.hmacInitF.2.2,
    initEntry_noResidue s.noResidue l.noResidue (by omega_using []) hn v.hBlock⟩

theorem initCodeA_spSafe (v : MdHash) (lv : VecLevel) :
    (initCodeA lv v.H v.I).all (fun i => !isa.writesSp i) = true := by
  have h₁ : (scrubAll lv ((Spec.Hmac.initSig v.I.S).retBits 64) (16 + initFrame v.H)
      (Impl.StackScratch.X86_64.withStackScratch (initFrame v.H) .r8 v.H.hmacInit)).all
      (fun i => !isa.writesSp i) = true := scrubKs_spSafe v.hmacShortFSp
  have h₂ : (scrubAll lv ((Spec.Hmac.initSig v.I.S).retBits 64) (24 + anyFrame v.H)
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame v.H) .r8 (anyWords v.H) v.H.hmacInitAny)).all
      (fun i => !isa.writesSp i) = true := scrubKs_spSafe v.hmacAnyFSp
  unfold initCodeA
  generalize scrubAll lv _ (16 + initFrame v.H) _ = a at h₁ ⊢
  generalize scrubAll lv _ (24 + anyFrame v.H) _ = b at h₂ ⊢
  simp only [Impl.Pbkdf2.Md.X86_64.initEntry, Code.iteCold, Code.all, h₁, h₂, Bool.and_true]
  rfl

/-- An implementation of HMAC's `init` for a key of any length, of instance
`I` (`vg_hmac_<hash>_init`): its code as emitted, cleanup included, and the
theorem about that code, which its registration binds. -/
structure InitImpl (I : Spec.Hmac.Instance) where
  /-- What follows the function's name. -/
  suffix : String
  /-- CPU features it is chosen only with, beyond those its code needs
  (`Registration.extra`): for an `init` that is faster only on some of the
  CPUs that can run it, which a feature its code does not use tells apart. -/
  extra : List String := []
  code : Prog isa
  /-- The bytes of stack it uses. -/
  stack : Nat
  scrubbed : VerifiedScrubbed target code (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64)
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-- HMAC's `init` over the variant `v`, `initCodeA` at the level `lv`, chosen
only with the features `extra` too, from what the cleanup of each branch
needs of its code, which the variant evaluates (`h₁`, `h₂`). -/
def MdHash.initSel (v : MdHash) (lv : VecLevel) (extra : List String) (hS : v.I.S.stateBytes < 2 ^ 64)
    (hn : 16 + initFrame v.H ≤ 24 + anyFrame v.H)
    (h₁ : scrubSideG v.shortPlain.code (16 + initFrame v.H) ((Spec.Hmac.initSig v.I.S).retBits 64) lv true
      (wipeKs (chunksA (16 + initFrame v.H))) (chunksA (16 + initFrame v.H))
      (gsAll (wipeKs (chunksA (16 + initFrame v.H)))) [] = true)
    (h₂ : scrubSideG v.anyPlain.code (24 + anyFrame v.H) ((Spec.Hmac.initSig v.I.S).retBits 64) lv true
      (wipeKs (chunksA (24 + anyFrame v.H))) (chunksA (24 + anyFrame v.H))
      (gsAll (wipeKs (chunksA (24 + anyFrame v.H)))) [] = true) : InitImpl v.I where
  suffix := v.suffix
  extra := extra
  code := initCodeA lv v.H v.I
  stack := 24 + anyFrame v.H
  scrubbed := initCodeA_scrubbed v lv hS hn h₁ h₂
  spSafe := initCodeA_spSafe v lv

end VG.Proof.Pbkdf2.Md.X86_64
