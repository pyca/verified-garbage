module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Poly1305.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueMx
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
meta import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Init
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Poly1305.BlocksScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Lit

/-!
# Poly1305 without secret residue (x86-64)

`init`, `update` (for each implementation of `vg_poly1305_blocks`) and
`finalize`, each followed by `Impl.Scrub.X86_64.scrubSel`
(`X86_64.Scrub.verifiedScrubbedSel`), which wipes the granules of its stack
the residue analysis finds may hold secrets. What that needs of their postconditions is that
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
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

theorem initOut (stack : Nat) : PostOut (initContract X86_64.abi stack) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (Nat.succ.inj hlen)
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    exact repr_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
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
    intro key msg hbf hc
    exact buffered_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega_using [hi])) (h key msg hbf hc)

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
      (by simp only [Elem.size]; omega_using [hi])]
    exact h key msg hbf hc

/-! ## The registrations -/

/-- `vg_poly1305_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize

open VG.X86_64.RScrub in
/-- `vg_poly1305_update` over the implementation `v` of `vg_poly1305_blocks`,
as a registration before its clearing. -/
def updatePlain (v : BlocksImpl) : Unscrubbed Spec.Poly1305.updateApi X86_64.target where
  suffix := v.suffix
  code := updateCode v.name v.code
  stack := 160
  verified := update_framed v
  spSafe := X86_64.withStackScratch_spSafe_of (update_spSafe v)

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Poly1305.X86_64.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Poly1305.initApi`'s function as emitted (`Impl.Poly1305.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Poly1305.X86_64.Fn.init (Spec.Poly1305.initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Poly1305.initApi)
    { code := Impl.Poly1305.X86_64.init
      verified := init_verified
      spSafe := init_codeSp }
    .sse [] (initOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Poly1305.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

theorem finalize_codeSp : (Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Poly1305.finalizeApi`'s function as emitted (`Impl.Poly1305.X86_64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Poly1305.X86_64.Fn.finalize (Spec.Poly1305.finalizeApi.contract X86_64.abi 136) 0 :=
  verifiedScrubbedSel (api := Spec.Poly1305.finalizeApi)
    { code := finalizeCode
      stack := 136
      verified := finalize_framed
      spSafe := finalize_codeSp }
    .sse [] (finalizeOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem finalize_spSafe : Impl.Poly1305.X86_64.Fn.finalize.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe finalize_codeSp

/-- `Spec.Poly1305.updateApi`'s function as emitted over the implementation
`v` of `vg_poly1305_blocks` (`Impl.Poly1305.X86_64.Fn.update`) meets its
contract in constant time and returns without secret residue: from the
analysis of `v.upd` (`rtaintMx`, which takes its calls of `vg_mcdt_enter`
as an operation). Where `v` loads MXCSR (in `vg_mcdt_enter`, on the path of
many blocks only), two runs along the same path leave the same MXCSR, so
the cleanup writes none. -/
theorem update_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.Poly1305.X86_64.Fn.update v.upd.level v.upd.runs v.name v.code)
      (Spec.Poly1305.updateApi.contract X86_64.abi 160) 0 :=
  have ⟨_, hS, hc⟩ := v.upd.ok
  verifiedScrubbedKs (updatePlain v) v.upd.level _ (updateOut _)
    (RScrub.resOk_regOpsA (updatePlain v) rfl (RScrub.pubOk_nil _) hS hc (show (Impl.Scrub.X86_64.chunksA 160).sum = 160 by decide)) v.upd.side rfl rfl

theorem updateFn_spSafe (v : BlocksImpl) :
    (Impl.Poly1305.X86_64.Fn.update v.upd.level v.upd.runs v.name v.code).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (X86_64.withStackScratch_spSafe_of (update_spSafe v))
end VG.Proof.Poly1305.X86_64
