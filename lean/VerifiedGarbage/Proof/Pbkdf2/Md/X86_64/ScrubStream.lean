module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset

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
  residue := (scrubReg f.reg v ks hd hst h8 hlv hrb hpost hres rfl).residue

theorem StreamFn.scrub_noResidue (f : StreamFn) (v : VecLevel) (ks : List Nat)
    (hd : f.code.x86_64Depth ≤ f.stack) (hst : f.stack + 8 < 2 ^ 64) (h8 : f.stack % 8 = 0)
    (hlv : f.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : f.retBits ≤ 32 ∨ f.retBits = 64) (hpost : PostOut f.contract f.retBits)
    (hres : ResOk f.code f.contract f.stack ks (chunks f.stack)) :
    NoResidue (f.scrub v ks hd hst h8 hlv hrb hpost hres).code f.contract f.retBits :=
  scrubReg_noResidue f.reg v ks hd hst h8 hlv hrb hpost hres rfl

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

end VG.Proof.Pbkdf2.Md.X86_64
