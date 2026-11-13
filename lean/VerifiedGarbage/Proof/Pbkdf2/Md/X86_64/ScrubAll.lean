module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# Functions over a variant that wipe their whole frame (x86-64)

For the functions over an `MdHash` whose code the residue analysis does
not follow, the clearing with every granule of their stack wiped
(`X86_64.Scrub.scrubRegAll`), which needs no analysis: the kernel checks
nothing of their code, and the emitter checks `scrub`'s side conditions
when it runs, at the lowest level that covers the code (`levelAll`).

* `StreamFn.scrubAuto`: a streaming function.
* `MdHash.hmacFinAuto`: HMAC's `finalize`, with the variant's residue
  analysis where it gives one (`MdHash.hmacFinReg`), otherwise wiping its
  frame.
* `MdHash.pbkdf2Reg`: PBKDF2's `pbkdf2`, which runs once per derived key, so
  wiping its whole frame costs nothing next to its iterations. Its
  postcondition reads the memory on return only within `out` (`pbkdf2Out`).

It is a module of its own, not part of `ScrubStream.lean`, so that the
residue analyses that import that module are not rebuilt for it.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `f` followed by the clearing with every granule of its stack wiped
(`StreamFn.scrub` with `allKs`), at the lowest level that covers its code
(`levelAll`), if `scrub`'s side conditions hold and the clearing needs no
CPU feature its code does not; otherwise `f`, which the emitter refuses
unless `ci/residue_allowlist.txt` lists it. For a streaming function whose
code the residue analysis does not follow. -/
def StreamFn.scrubAuto (f : StreamFn) (hpost : PostOut f.contract f.retBits) : StreamFn :=
  let v := levelAll f.code
  if hne : v ≠ .evex then
  if hd : f.code.x86_64Depth ≤ f.stack then
  if hst : f.stack + 8 < 2 ^ 64 then
  if h8 : f.stack % 8 = 0 then
  if hlv : f.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
  if hrb : f.retBits ≤ 32 ∨ f.retBits = 64 then
    let f' := f.scrub v (allKs (chunks f.stack)) hd hst h8 hlv hrb hpost (resOk_all _ _ h8) hne
    if (Code.requiresDedup isa.requires f'.code).all
        (fun g => (Code.requiresDedup isa.requires f.code).contains g) then f' else f
  else f else f else f else f else f else f

/-- HMAC's `finalize` over the variant `v`: `MdHash.hmacFinReg` where `v`
gives the residue analysis of its code (`MdHash.hmacFinRes`), otherwise the
same followed by the clearing with every granule of its stack wiped
(`withScrubAll`). -/
def MdHash.hmacFinAuto (v : MdHash) : Registration v.I.finalizeApi target :=
  if v.hmacFinRes.isSome then v.hmacFinReg else
  if hD : v.I.S.digestBytes < 2 ^ 64 then
    withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch (hmacFrame v.H) .r8 v.H.hmacFin
      stack := 16 + hmacFrame v.H
      verified := v.hmacFinF
      spSafe := X86_64.withStackScratch_spSafe_of v.hmacFinSp } (hmacFinOut v.I hD _)
  else v.hmacFinReg

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega) (by omega))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega)]
    exact h

/-- PBKDF2's `pbkdf2` over the variant `v`: `pbkdf2` with its working space
in a frame of its own, followed by the clearing with every granule of its
stack wiped (`withScrubAll`). -/
def MdHash.pbkdf2Reg (v : MdHash) : Registration v.I.pbkdf2Api target :=
  withScrubAll {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame v.H) 1 v.H.pbkdf2
    stack := 24 + pbkdf2Frame v.H
    verified := v.pbkdf2F
    spSafe := X86_64.withStackArgScratch_spSafe v.pbkdf2Sp } (pbkdf2Out v.I _)

end VG.Proof.Pbkdf2.Md.X86_64
