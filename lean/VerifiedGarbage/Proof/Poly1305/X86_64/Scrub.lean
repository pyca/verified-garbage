module

public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
public import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
meta import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Init
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
meta import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Poly1305.BlocksScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Lit

/-!
# Poly1305 without secret residue (x86-64)

`init`, `update` (for each implementation of `vg_poly1305_blocks`) and
`finalize`, each scrubbed where the residue analysis allows it
(`X86_64.RScrub.autoScrub`). What that needs of their postconditions is that
they read the memory on return only within the buffers
(`X86_64.Scrub.PostOut`): the streaming state is bytes of the state buffer
(`repr_congr`, `buffered_congr`), the tag bytes of `out`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG.Spec.Poly1305 VG.X86_64 VG.X86_64.Scrub

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega) (by omega))).symm

theorem initOut (stack : Nat) : PostOut (initContract X86_64.abi stack) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (Nat.succ.inj hlen)
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    exact repr_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega)) h

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
    intro key msg hbf hc
    exact buffered_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega)) (h key msg hbf hc)

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
    intro key msg hbf hc
    show bytesAt m₂ ot 16 = _
    rw [bytesAt_congr' fun i hi => agreeBuf (n := 16 * Elem.size .u8) (by decide) hb.2 i
      (by simp only [Elem.size]; omega)]
    exact h key msg hbf hc

/-! ## The registrations -/

/-- `vg_poly1305_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize

def initKs : List Nat := keep_for% Spec.Poly1305.initApi.sig 0 Impl.Poly1305.X86_64.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Poly1305.initApi.sig 0 []) Impl.Poly1305.X86_64.init
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

def finalizeKs : List Nat := keep_for% Spec.Poly1305.finalizeApi.sig 136 finalizeCode []

theorem finalizeOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Poly1305.finalizeApi.sig 136 []) finalizeCode
      h).any (RScrub.resOkB · 136 finalizeKs (Impl.Scrub.X86_64.chunks 136)) = true :=
  RScrub.Analysed.ok_of finalizeKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_poly1305_init`. -/
def initReg : Registration Spec.Poly1305.initApi X86_64.target :=
  withScrub { code := Impl.Poly1305.X86_64.init, verified := init_verified } (initOut _) [] (pubOk_nil _)
    (some ⟨initKs, initOk⟩)

open VG.X86_64.RScrub in
/-- `vg_poly1305_finalize`. -/
def finalizeReg : Registration Spec.Poly1305.finalizeApi X86_64.target :=
  withScrub {
    code := finalizeCode
    stack := 136
    verified := finalize_framed } (finalizeOut _) [] (pubOk_nil _) (some ⟨finalizeKs, finalizeOk⟩)

open VG.X86_64.RScrub in
/-- `vg_poly1305_update` over the implementation `v` of `vg_poly1305_blocks`:
without secret residue where `v` gives its analysis (`BlocksImpl.update`). -/
def updateReg (v : BlocksImpl) : Registration Spec.Poly1305.updateApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := updateCode v.name v.code
    stack := 160
    verified := update_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (update_spSafe v)
    features := v.features } (updateOut _) [] (pubOk_nil _) v.update

end VG.Proof.Poly1305.X86_64
