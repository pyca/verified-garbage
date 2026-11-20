module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# PBKDF2 over a variant, wiping its whole frame (x86-64)

`Pbkdf2Impl`: PBKDF2's `pbkdf2` over an `MdHash`, whose code the residue
analysis does not follow (it reloads `out_len` from a frame slot the
analysis loses), followed by the cleanup with every granule of its stack
wiped (`Impl.Scrub.X86_64.scrubAll`), which needs no analysis, only the
cleanup's side conditions of its code, which the variant evaluates. It runs once per derived key, so wiping its whole
frame costs nothing next to its iterations. Its postcondition reads the
memory on return only within `out` (`pbkdf2Out`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

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
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega_using [hi])]
    exact h

/-- PBKDF2's `pbkdf2` over the variant `v`: `pbkdf2` with its working space
in a frame of its own (`MdHash.pbkdf2F`), with what its cleanup, which wipes
every granule of its stack (`Impl.Scrub.X86_64.scrubAll`), needs of its code:
the level of its vector registers and the cleanup's other conditions
(`side`), which the variant evaluates once (by `lit_decide`). -/
structure Pbkdf2Impl where
  v : MdHash
  level : VecLevel
  side : scrubSideG (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame v.H) 1 v.H.pbkdf2)
    (24 + pbkdf2Frame v.H) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) level true
    (wipeKs (chunksA (24 + pbkdf2Frame v.H))) (chunksA (24 + pbkdf2Frame v.H))
    (gsAll (wipeKs (chunksA (24 + pbkdf2Frame v.H)))) [] = true

/-- `p`'s function before its cleanup. -/
def Pbkdf2Impl.plain (p : Pbkdf2Impl) : Unscrubbed p.v.I.pbkdf2Api target where
  suffix := p.v.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame p.v.H) 1 p.v.H.pbkdf2
  stack := 24 + pbkdf2Frame p.v.H
  verified := p.v.pbkdf2F
  spSafe := X86_64.withStackArgScratch_spSafe p.v.pbkdf2Sp

/-- `p`'s code as emitted, its code and then its cleanup, meets its contract
in constant time and returns without secret residue. -/
theorem Pbkdf2Impl.scrubbed (p : Pbkdf2Impl) :
    VerifiedScrubbed target
      (scrubAll p.level (Spec.Pbkdf2.pbkdf2Sig.retBits 64) (24 + pbkdf2Frame p.v.H) p.plain.code)
      p.plain.contract (Spec.Pbkdf2.pbkdf2Sig.retBits 64) :=
  verifiedScrubbedAll p.plain p.level (pbkdf2Out p.v.I _) p.side

/-- `p` as a registration of its `Api` (`Api.artifact`): its code as emitted,
with its cleanup, and the theorem about that code (`Pbkdf2Impl.scrubbed`). -/
def Pbkdf2Impl.reg (p : Pbkdf2Impl) : Registration p.v.I.pbkdf2Api target where
  suffix := p.v.suffix
  consts := []
  tables := []
  code := scrubAll p.level (Spec.Pbkdf2.pbkdf2Sig.retBits 64) (24 + pbkdf2Frame p.v.H) p.plain.code
  contract := p.plain.contract
  stack := p.plain.stack
  verified := .scrubbed p.scrubbed
  ofApi := p.plain.ofApi
  ofSig := p.plain.ofSig
  spSafe := scrubKs_spSafe p.plain.spSafe

end VG.Proof.Pbkdf2.Md.X86_64
