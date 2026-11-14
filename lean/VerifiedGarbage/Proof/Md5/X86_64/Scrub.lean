module

public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Md5.X86_64.Lit
meta import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Md5.X86_64.Shared
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Md5.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Md5.X86_64.Lit

/-!
# MD5's streaming functions on x86-64, without secret residue

`vg_md5_init`, `vg_md5_update` and `vg_md5_finalize`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. HMAC-MD5 and PBKDF2-HMAC-MD5 call
`vg_md5_init`'s code as the internal `vg_md5_init_core`
(`Proof.Pbkdf2.Md.X86_64.Md5.hash`), which clears what it leaves itself. Their postconditions read the memory on
return only within the buffers (`X86_64.Scrub.PostOut`): the streaming state (`Stream.repr_congr`) and the digest.
-/

@[expose] public section

namespace VG.Proof.Md5.X86_64

open VG.Spec.Md5 VG.X86_64 VG.X86_64.Scrub

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    exact Stream.repr_congr (fun i hi => agreeBuf (n := 80 * Elem.size .u8) (by decide) hb i
      (by simp only [Elem.size]; omega_using [hi])) h

theorem updateOut (stack : Nat) : PostOut (updateContract X86_64.abi stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    intro msg hr hc
    exact Stream.repr_congr (fun i hi => agreeBuf (n := 80 * Elem.size .u8) (by decide) hb.1 i
      (by simp only [Elem.size]; omega_using [hi])) (h msg hr hc)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86_64.abi stack) (finalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    intro msg hr hc
    show bytesAt m₂ ot 16 = _
    rw [Stream.bytesAt_congr fun i hi => agreeBuf (n := 16 * Elem.size .u8) (by decide) hb.2 i
      (by simp only [Elem.size]; omega_using [hi])]
    exact h msg hr hc

/-! ## The registrations -/

/-- `vg_md5_update`'s code. -/
abbrev updateCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 56 .r8 Impl.Md5.X86_64.Stream.update

/-- `vg_md5_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 56 .rcx Impl.Md5.X86_64.Stream.finalize

def initKs : List Nat := keep_for% Spec.Md5.initApi.sig 0 Impl.Md5.X86_64.Stream.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Md5.initApi.sig 0 []) Impl.Md5.X86_64.Stream.init
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

def updateKs : List Nat := keep_for% Spec.Md5.updateApi.sig (8 + 56) updateCode []

theorem updateOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Md5.updateApi.sig (8 + 56) []) updateCode
      h).any (RScrub.resOkB · (8 + 56) updateKs (Impl.Scrub.X86_64.chunks (8 + 56))) = true :=
  RScrub.Analysed.ok_of updateKs (by taint_decide)

def finalizeKs : List Nat := keep_for% Spec.Md5.finalizeApi.sig (8 + 56) finalizeCode []

theorem finalizeOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Md5.finalizeApi.sig (8 + 56) []) finalizeCode
      h).any (RScrub.resOkB · (8 + 56) finalizeKs (Impl.Scrub.X86_64.chunks (8 + 56))) = true :=
  RScrub.Analysed.ok_of finalizeKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_md5_init`. -/
def initReg : Registration Spec.Md5.initApi X86_64.target :=
  withScrub { code := Impl.Md5.X86_64.Stream.init, verified := Shared.init } initOut []
    (pubOk_nil _) (some ⟨initKs, initOk⟩)

open VG.X86_64.RScrub in
/-- `vg_md5_update`. -/
def updateReg : Registration Spec.Md5.updateApi X86_64.target :=
  withScrub {
    code := updateCode
    stack := 8 + 56
    verified := Shared.update } (updateOut _) [] (pubOk_nil _) (some ⟨updateKs, updateOk⟩)

open VG.X86_64.RScrub in
/-- `vg_md5_finalize`. -/
def finalizeReg : Registration Spec.Md5.finalizeApi X86_64.target :=
  withScrub {
    code := finalizeCode
    stack := 8 + 56
    verified := Shared.finalize } (finalizeOut _) [] (pubOk_nil _) (some ⟨finalizeKs, finalizeOk⟩)

end VG.Proof.Md5.X86_64
