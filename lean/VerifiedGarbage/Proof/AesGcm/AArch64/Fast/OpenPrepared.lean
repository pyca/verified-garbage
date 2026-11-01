module

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared8
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Prepared

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_prepared`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_prepared` is
`open` with the path for TLS records (`Impl/AesGcm/AArch64/Fast.lean`), its
whole blocks hashed by `vg_ghash_prepared` (`GhashPreparedImpl`), as
`vg_aes_gcm_seal_prepared` is `seal`'s (`Fast/Prepared.lean`): the proofs of
`open` hold for such a call (`openWith_wp`, `openWith_ct`) with the
context's 384 bytes readable beside its first 256 (`openPrepN`,
`openPreX`), where the call finds the prepared powers (`gpCallO_of`); the
shared contract's states (`openPrepW`) narrow to those regions (`narrowO`),
and the code runs from them as it does with both, with the same trace.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- What `vg_aes_gcm_open_prepared` needs, on the regions its proofs run on:
`openPreX` with the 384 bytes of the context readable too, apart from the
text and the working space, holding the prepared powers. -/
def openPrepN (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 384⟩
  openPreX [ctx] s ∧ ctx.Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧ ctx.Disjoint ⟨stackArg s 2, 2560⟩ ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0)

/-- What `vg_aes_gcm_open_prepared` needs: `openPreX`, with the 384 bytes of
the context readable in place of its first 256, holding the prepared powers. -/
def openPrepW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 384⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 3] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ tag.Disjoint work ∧ work.Disjoint (args s 3) ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0)

/-- `vg_aes_gcm_open_prepared`. -/
def openPreparedAArch64 : Contract isa where
  pre := openPrepW
  post := openAArch64.post
  pub := openAArch64.pub

/-- At the call of `vg_ghash_prepared`, with memory changed since the entry
only in the working space and the text: the prepared context is readable,
apart from the accumulator and the working space of the call, and holds the
prepared powers. -/
theorem gpCallO_of {σ s : State} {Ctx W D Y Dd S : Addr} {n nb : Nat} (hs : openPrepN σ)
    (hC : σ.gpr .x0 = Ctx) (hW : stackArg σ 2 = W) (hD : σ.gpr .x6 = D) (hn : (σ.gpr .x7).toNat = n)
    (hc : GhCall s (Ctx + BitVec.ofNat 64 240) Y Dd S nb) (sY : Region.Sub ⟨Y, 16⟩ (workR W))
    (sS : Region.Sub ⟨S, 256⟩ (workR W)) (hrd : s.rd = σ.rd) (hf : Frame [workR W, ⟨D, n⟩] σ.mem s.mem) :
    GhPCall s Ctx Y S := by
  subst hC hW hD hn
  obtain ⟨hpx, cd, cw, -, rep⟩ := hs
  have hrd₀ := hpx.1
  have sub : Region.Sub ⟨σ.gpr .x0 + BitVec.ofNat 64 240, 144⟩ ⟨σ.gpr .x0, 384⟩ := Offset.sub_base _ (by decide)
  refine ⟨?_, (cw.sub_left sub).sub_right sY, (cw.sub_left sub).sub_right sS, ?_⟩
  · refine Covers.left (Covers.of_sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, by rw [hrd, hrd₀]; exact List.mem_append_right _ (List.mem_singleton_self _), 240, rfl,
      show 240 + 144 ≤ 384 by decide⟩
  · refine Proof.AesGcm.preparedPowers8Repr_congr (fun i hi => hf _ fun r hr hcon => ?_) rep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hx := Offset.contains_base (σ.gpr .x0) (show i + 1 ≤ 384 by omega) (by omega)
    rcases hr with rfl | rfl
    · exact cw _ hx hcon
    · exact cd _ hx hcon

/-! ## On the regions of the proofs -/

section
variable (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openPrepared_correctN (s : State) (hs : openPrepN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn) s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' :=
  WP.withPreservedV (openWith_wp gp.fn v hMK hs.1 fun _ _ _ _ _ hc sY sS hrd _ hf =>
    gp_call hc (gpCallO_of hs rfl rfl rfl rfl hc sY sS hrd hf) gp) (fastOpenWith_keepsV v gp.keepsV)

theorem openPrepared_ctN :
    ConstantTime isa openPrepN openAArch64.pub (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn) :=
  openWith_ct v gp.fn hMK (extra := fun s => [⟨s.gpr .x0, 384⟩]) (fun _ h => h.1)
    (fun hs hc sY sS hrd _ hf => gp_call hc (gpCallO_of hs rfl rfl rfl rfl hc sY sS hrd hf) gp)
    fun p₁ p₂ hq c₁ c₂ sY sS sp r₁ _ f₁ r₂ _ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, -, qa⟩ := hq
      exact gp_rel gp c₁ (gpCallO_of p₁ rfl rfl rfl rfl c₁ sY sS r₁ f₁) c₂
        (gpCallO_of p₂ q0.symm (qa 2 (by decide)).symm q6.symm (by rw [q7]) c₂ sY sS r₂ f₂) sp

end

/-! ## On the shared contract's regions -/

/-- The readable regions of the proofs: the context's first 256 bytes, the
nonce, the additional data, the tag, the stack arguments and the context's
384. -/
def narrowRdO (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s 3, ⟨s.gpr .x0, 384⟩]

/-- `s` with the readable regions of the proofs. -/
def narrowO (s : State) : State := s.withRegions (narrowRdO s) s.wr

theorem narrowO_pre {s : State} (h : openPrepW s) : openPrepN (narrowO s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, dw, da, tw, wa, b0, b2, b4, b6, b1, bsp, hr, rep⟩ := h
  have sub : Region.Sub ⟨s.gpr .x0, 256⟩ ⟨s.gpr .x0, 384⟩ := Region.sub_prefix (by decide)
  exact ⟨⟨rfl, hwr, cd.sub_left sub, cw.sub_left sub, nd, nw, ad, aw, dw, da, tw, wa,
    show (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 by omega, b2, b4, b6, b1, bsp, hr⟩, cd, cw, b0, rep⟩

theorem narrowO_covers {s : State} (h : openPrepW s) :
    Covers ((narrowO s).rd ++ (narrowO s).wr) (s.rd ++ s.wr) := by
  rw [show (narrowO s).rd = narrowRdO s from rfl, show (narrowO s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.cons ?_ (Covers.of_mem fun r hr => ?_)) (Covers.refl _)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_cons_self .., 0, by simp, show 0 + 256 ≤ 384 by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

theorem narrowO_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : openPrepW s)
    (he : Exec isa c (narrowO s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowO_covers h) (Covers.refl _)
  rwa [show (narrowO s).withRegions s.rd s.wr = s from rfl] at this

section
variable (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openPrepared_correct (s : State) (hs : openPreparedAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn) s t s' ∧ abiPreserved s s' ∧
      openPreparedAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openPrepared_correctN v gp hMK _ (narrowO_pre hs)
  exact ⟨t, _, narrowO_exec hs he, ha, hp⟩

theorem openPrepared_ct :
    ConstantTime isa openPreparedAArch64.pre openPreparedAArch64.pub
      (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openPrepared_correctN v gp hMK _ (narrowO_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openPrepared_correctN v gp hMK _ (narrowO_pre h₂)
  rw [(Exec.det e₁ (narrowO_exec h₁ f₁)).1, (Exec.det e₂ (narrowO_exec h₂ f₂)).1]
  exact openPrepared_ctN v gp hMK _ _ _ _ _ _ (narrowO_pre h₁) (narrowO_pre h₂) hq f₁ f₂

/-- A state satisfying `vg_aes_gcm_open_prepared`'s precondition: `openSat`
with the context's 384 bytes, all zero. -/
def openSatP : State :=
  { openSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] }

theorem openPrepared_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn)
      (Proof.AesGcm.openPrepared8ScratchContract AArch64.abi) :=
  Verified.of_correct (openPrepared_correct v gp hMK) (openPrepared_ct v gp hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openPrepared8ScratchContract, Proof.AesGcm.openPrepared8ScratchSig,
          Proof.Gcm.openPrepared8Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
          openPreparedAArch64, openPrepW, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openPrepared8ScratchContract, Proof.AesGcm.openPrepared8ScratchSig,
          Proof.Gcm.openPrepared8Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
          openPreparedAArch64, openPrepW, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openPrepared8ScratchContract, Proof.AesGcm.openPrepared8ScratchSig,
          Proof.Gcm.openPrepared8Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
          openPreparedAArch64, openPrepW, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨openSatP, by
        sig_pre [Proof.AesGcm.openPrepared8ScratchContract, Proof.AesGcm.openPrepared8ScratchSig,
          Proof.Gcm.openPrepared8Pre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, openSatP, openSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (refine Proof.AesGcm.preparedPowers8Repr_of_zeroMem fun i hi => ?_
             split
             · next h => exfalso; bv_omega
             · rfl)⟩ }

end

/-! ## With its working space on the stack -/

/-- `openFrameSat` with the context's 384 bytes. -/
def openFrameSatP : State :=
  { openFrameSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] }

theorem openFrameSatP_pre : ∃ s, (Proof.Gcm.openPrepared8Contract AArch64.abi 2592).pre s := by
  refine ⟨openFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.openPrepared8Contract, Proof.Gcm.openPrepared8Sig,
    Proof.Gcm.openPrepared8Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, openFrameSatP, openFrameSat,
    openSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Proof.AesGcm.preparedPowers8Repr_of_zeroMem fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem openPrepared_framed (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn))
      (Proof.Gcm.openPrepared8Contract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Proof.Gcm.openPrepared8Sig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.openPrepared8Pre AArch64.abi.ptrBits)
    (post := Spec.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openLeak AArch64.abi.ptrBits))
    (openPrepared_verified v gp hMK) (by decide) (by decide) (Proof.AesGcm.openPrepared8Pre_local _)
    (Proof.AesGcm.openPrepared8Post_local _) openFrameSatP_pre (hleak := Proof.AesGcm.openPrepared8Leak_local _)

end VG.Proof.AesGcm.AArch64.Fast
