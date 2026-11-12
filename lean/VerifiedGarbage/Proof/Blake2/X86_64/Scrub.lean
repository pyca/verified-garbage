module

public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Blake2.X86_64.Backend
meta import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT

/-!
# BLAKE2b's and BLAKE2s's streaming functions on x86-64, without secret residue

`vg_blake2b_init` and `vg_blake2s_init`, and `vg_blake2b_update`, `vg_blake2b_finalize` and BLAKE2s's, over each backend,
each followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`)
where the backend gives the residue analysis of its code
(`Backend.updateRes`, `Backend.finalizeRes`). Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
streaming state (`repr_congr'`) and the digest (`bytesAt_congr`).
Argon2 calls `vg_blake2b_init`'s code as the internal `vg_blake2b_init_core`
(`Proof.Argon2.X86_64.HPrime.hash`).
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.Spec.Blake2

theorem updateBPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateBSig.words pb).length →
    (∀ b ∈ Sig.bufs updateBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateBSig.words pb) (updateBPost pb) vs m m₁ r →
      Curry.apply (updateBSig.words pb) (updateBPost pb) vs m m₂ r
  | [st, ct, dt, ln], m, m₁, m₂, r, _, hb, h => by
    simp only [updateBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    intro h0 d hr hc hl
    exact repr_congr' (by decide)
      (fun i hi => hs i (by simp only [bufOff, blockBytes] at hi; omega_arith)) (h h0 d hr hc hl)

theorem finalizeBPost_out (pb : Nat) :
    ∀ vs m m₁ m₂ r, vs.length = (finalizeBSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m m₁ r →
        Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m m₂ r
  | [st, ct, ot], m, m₁, m₂, r, _, hb, h => by
    simp only [finalizeBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have ho : ∀ i < 64, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
      (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    intro h0 d hr hl hc
    show bytesAt m₂ ot 64 = _
    rw [bytesAt_congr ho]
    exact h h0 d hr hl hc

theorem updateSPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSSig.words pb) (updateSPost pb) vs m m₁ r →
      Curry.apply (updateSSig.words pb) (updateSPost pb) vs m m₂ r
  | [st, ct, dt, ln], m, m₁, m₂, r, _, hb, h => by
    simp only [updateSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    intro h0 d hr hc hl
    exact repr_congr' (by decide)
      (fun i hi => hs i (by simp only [bufOff, blockBytes] at hi; omega_arith)) (h h0 d hr hc hl)

theorem finalizeSPost_out (pb : Nat) :
    ∀ vs m m₁ m₂ r, vs.length = (finalizeSSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m m₁ r →
        Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m m₂ r
  | [st, ct, ot], m, m₁, m₂, r, _, hb, h => by
    simp only [finalizeSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have ho : ∀ i < 32, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
      (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    intro h0 d hr hl hc
    show bytesAt m₂ ot 32 = _
    rw [bytesAt_congr ho]
    exact h h0 d hr hl hc

end VG.Proof.Blake2

namespace VG.Proof.Blake2.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem updateBOut (stack : Nat) :
    PostOut (Spec.Blake2.updateBContract X86_64.abi stack) (Spec.Blake2.updateBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (updateBPost_out 64)

theorem finalizeBOut (stack : Nat) :
    PostOut (Spec.Blake2.finalizeBContract X86_64.abi stack) (Spec.Blake2.finalizeBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (finalizeBPost_out 64)

theorem updateSOut (stack : Nat) :
    PostOut (Spec.Blake2.updateSContract X86_64.abi stack) (Spec.Blake2.updateSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (updateSPost_out 64)

theorem finalizeSOut (stack : Nat) :
    PostOut (Spec.Blake2.finalizeSContract X86_64.abi stack) (Spec.Blake2.finalizeSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (finalizeSPost_out 64)

theorem initBOut : PostOut (Spec.Blake2.initBContract X86_64.abi) (Spec.Blake2.initBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Blake2.initBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    exact repr_congr' (by decide)
      (fun i hi => hs i (by simp only [bufOff, Spec.Blake2.blockBytes] at hi; omega_arith)) h

theorem initSOut : PostOut (Spec.Blake2.initSContract X86_64.abi) (Spec.Blake2.initSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Blake2.initSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
    exact repr_congr' (by decide)
      (fun i hi => hs i (by simp only [bufOff, Spec.Blake2.blockBytes] at hi; omega_arith)) h

/-! ## The registrations -/

def initBKs : List Nat := keep_for% Spec.Blake2.initBApi.sig 0 (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b) []

theorem initBOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blake2.initBApi.sig 0 [])
      (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b)
      h).any (RScrub.resOkB · 0 initBKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initBKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blake2b_init`. -/
def initBReg : Registration Spec.Blake2.initBApi X86_64.target :=
  withScrub {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.X86_64.Stream.initB_verified } initBOut [] (pubOk_nil _) (some ⟨initBKs, initBOk⟩)

def initSKs : List Nat := keep_for% Spec.Blake2.initSApi.sig 0 (Impl.Blake2.X86_64.Stream.init Spec.Blake2.s) []

theorem initSOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blake2.initSApi.sig 0 [])
      (Impl.Blake2.X86_64.Stream.init Spec.Blake2.s)
      h).any (RScrub.resOkB · 0 initSKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initSKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blake2s_init`. -/
def initSReg : Registration Spec.Blake2.initSApi X86_64.target :=
  withScrub {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.X86_64.Stream.initS_verified } initSOut [] (pubOk_nil _) (some ⟨initSKs, initSOk⟩)

open VG.X86_64.RScrub in
/-- `vg_blake2b_update` over the backend `v`: without secret residue where `v`
gives its analysis (`Backend.updateRes`). -/
def updateBReg (v : Backend) : Registration Spec.Blake2.updateBApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    stack := 8 + 584
    verified := v.update_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe } (updateBOut _) [] (pubOk_nil _)
    v.updateRes

open VG.X86_64.RScrub in
/-- `vg_blake2b_finalize` over the backend `v` (`Backend.finalizeRes`). -/
def finalizeBReg (v : Backend) : Registration Spec.Blake2.finalizeBApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    stack := 8 + 584
    verified := v.finalize_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe } (finalizeBOut _) [] (pubOk_nil _)
    v.finalizeRes

open VG.X86_64.RScrub in
/-- `vg_blake2s_update` over the backend `v` (`BackendS.updateRes`). -/
def updateSReg (v : BackendS) : Registration Spec.Blake2.updateSApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    stack := 8 + 584
    verified := v.update_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe } (updateSOut _) [] (pubOk_nil _)
    v.updateRes

open VG.X86_64.RScrub in
/-- `vg_blake2s_finalize` over the backend `v` (`BackendS.finalizeRes`). -/
def finalizeSReg (v : BackendS) : Registration Spec.Blake2.finalizeSApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    stack := 8 + 584
    verified := v.finalize_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe } (finalizeSOut _) [] (pubOk_nil _)
    v.finalizeRes

end VG.Proof.Blake2.X86_64
