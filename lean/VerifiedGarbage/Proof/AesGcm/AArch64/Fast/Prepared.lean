module

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared8
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal_prepared`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_prepared` is
`seal` with the path for TLS records (`Impl/AesGcm/AArch64/Fast.lean`), its
whole blocks hashed by `vg_ghash_prepared` (`GhashPreparedImpl`), which reads
the powers of `H` from the prepared context instead of computing them. The
proofs of `seal` hold for any such call that hashes as `vg_ghash` and leaks
the same in two runs (`sealWith_wp`, `sealWith_ct`), given the context's 384
bytes readable beside its first 256 (`sealPrepN`, `sealPreX`): the call
reads them, apart from what the code before it wrote (the working space and
the text), and so finds the prepared powers there (`gpCall_of`).

The shared contract lets the code read the context's 384 bytes in place of
its first 256 (`sealPrepW`): the code runs as it does with both (`narrow`,
`Exec.widen`), with the same trace.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- What `vg_aes_gcm_seal_prepared` needs, on the regions its proofs run on:
`sealPreX` with the 384 bytes of the context readable too, apart from the
text and the working space, holding the prepared powers. -/
def sealPrepN (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 384⟩
  sealPreX [ctx] s ∧ ctx.Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧ ctx.Disjoint ⟨stackArg s 1, 2560⟩ ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0)

/-- What `vg_aes_gcm_seal_prepared` needs: `sealPreX`, with the 384 bytes of
the context readable in place of its first 256, holding the prepared powers. -/
def sealPrepW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 384⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧
    data.Disjoint work ∧ data.Disjoint (args s 2) ∧ tag.Disjoint work ∧ work.Disjoint (args s 2) ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 2 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0)

/-- `vg_aes_gcm_seal_prepared`. -/
def sealPreparedAArch64 : Contract isa where
  pre := sealPrepW
  post := sealAArch64.post
  pub := onePub 2

/-! ## The call of `vg_ghash_prepared` -/

/-- At the call of `vg_ghash_prepared`, with memory changed since the entry
only in the working space and the text: the prepared context is readable,
apart from the accumulator and the working space of the call, and holds the
prepared powers. -/
theorem gpCall_of {σ s : State} {Ctx W D Y Dd S : Addr} {n nb : Nat} (hs : sealPrepN σ)
    (hC : σ.gpr .x0 = Ctx) (hW : stackArg σ 1 = W) (hD : σ.gpr .x6 = D) (hn : (σ.gpr .x7).toNat = n)
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

theorem sealPrepared_wp {s : State} (hs : sealPrepN s) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  sealWith_wp v gp.fn hMK hs.1 fun _ _ _ _ _ hc sY sS hrd _ hf =>
    gp_call hc (gpCall_of hs rfl rfl rfl rfl hc sY sS hrd hf) gp

theorem sealPrepared_correctN (s : State) (hs : sealPrepN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn) s t s' ∧ abiPreserved s s' ∧
      sealAArch64.post s s' :=
  WP.withPreservedV (sealPrepared_wp v gp hMK hs) (fastSealWith_keepsV v gp.keepsV)

theorem sealPrepared_ctN :
    ConstantTime isa sealPrepN sealAArch64.pub (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn) :=
  sealWith_ct v gp.fn hMK (fun _ h => h.1)
    (fun hs hc sY sS hrd _ hf => gp_call hc (gpCall_of hs rfl rfl rfl rfl hc sY sS hrd hf) gp)
    fun p₁ p₂ hq c₁ c₂ sY sS sp r₁ _ f₁ r₂ _ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, -, qa⟩ := hq
      exact gp_rel gp c₁ (gpCall_of p₁ rfl rfl rfl rfl c₁ sY sS r₁ f₁) c₂
        (gpCall_of p₂ q0.symm (qa 1 (by decide)).symm q6.symm (by rw [q7]) c₂ sY sS r₂ f₂) sp

end

/-! ## On the shared contract's regions -/

/-- The readable regions of the proofs: the context's first 256 bytes, the
nonce, the additional data, the stack arguments and the context's 384. -/
def narrowRd (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩, args s 2,
    ⟨s.gpr .x0, 384⟩]

/-- `s` with the readable regions of the proofs. -/
def narrow (s : State) : State := s.withRegions (narrowRd s) s.wr

theorem narrow_pre {s : State} (h : sealPrepW s) : sealPrepN (narrow s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, dt, dw, da, tw, wa, b0, b2, b4, b6, b1, bsp, hr, rep⟩ := h
  have sub : Region.Sub ⟨s.gpr .x0, 256⟩ ⟨s.gpr .x0, 384⟩ := Region.sub_prefix (by decide)
  exact ⟨⟨rfl, hwr, cd.sub_left sub, cw.sub_left sub, nd, nw, ad, aw, dt, dw, da, tw, wa, show (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 by omega, b2, b4, b6,
    b1, bsp, hr⟩, cd, cw, b0, rep⟩

theorem narrow_covers {s : State} (h : sealPrepW s) : Covers ((narrow s).rd ++ (narrow s).wr) (s.rd ++ s.wr) := by
  rw [show (narrow s).rd = narrowRd s from rfl, show (narrow s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.cons ?_ (Covers.of_mem fun r hr => ?_)) (Covers.refl _)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_cons_self .., 0, by simp, show 0 + 256 ≤ 384 by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : sealPrepW s) (he : Exec isa c (narrow s) t s₁) :
    Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrow_covers h) (Covers.refl _)
  rwa [show (narrow s).withRegions s.rd s.wr = s from rfl] at this

section
variable (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem sealPrepared_correct (s : State) (hs : sealPreparedAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn) s t s' ∧ abiPreserved s s' ∧
      sealPreparedAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := sealPrepared_correctN v gp hMK _ (narrow_pre hs)
  exact ⟨t, _, narrow_exec hs he, ha, hp⟩

theorem sealPrepared_ct :
    ConstantTime isa sealPreparedAArch64.pre sealPreparedAArch64.pub
      (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := sealPrepared_correctN v gp hMK _ (narrow_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := sealPrepared_correctN v gp hMK _ (narrow_pre h₂)
  rw [(Exec.det e₁ (narrow_exec h₁ f₁)).1, (Exec.det e₂ (narrow_exec h₂ f₂)).1]
  exact sealPrepared_ctN v gp hMK _ _ _ _ _ _ (narrow_pre h₁) (narrow_pre h₂) hq f₁ f₂

/-- A state satisfying `vg_aes_gcm_seal_prepared`'s precondition: `sealSat`
with the context's 384 bytes, all zero. -/
def sealSatP : State :=
  { sealSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩] }

theorem sealPrepared_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn)
      (Proof.AesGcm.sealPrepared8ScratchContract AArch64.abi) :=
  Verified.of_correct (sealPrepared_correct v gp hMK) (sealPrepared_ct v gp hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealPrepared8ScratchContract, Proof.AesGcm.sealPrepared8ScratchSig,
          Proof.Gcm.sealPrepared8Pre, Spec.Gcm.sealPost, sealPreparedAArch64,
          sealPrepW, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.sealPrepared8ScratchContract, Proof.AesGcm.sealPrepared8ScratchSig,
          Proof.Gcm.sealPrepared8Pre, Spec.Gcm.sealPost, sealPreparedAArch64,
          sealPrepW, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealPrepared8ScratchContract, Proof.AesGcm.sealPrepared8ScratchSig,
          Proof.Gcm.sealPrepared8Pre, Spec.Gcm.sealPost, sealPreparedAArch64,
          sealPrepW, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨sealSatP, by
        sig_pre [Proof.AesGcm.sealPrepared8ScratchContract, Proof.AesGcm.sealPrepared8ScratchSig,
          Proof.Gcm.sealPrepared8Pre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, sealSatP, sealSat,
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

/-- `sealFrameSat` with the context's 384 bytes. -/
def sealFrameSatP : State :=
  { sealFrameSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩] }

theorem sealFrameSatP_pre : ∃ s, (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576).pre s := by
  refine ⟨sealFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig,
    Proof.Gcm.sealPrepared8Pre, Spec.Gcm.sealPost, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
    AArch64.stackArgAddr, List.getD, List.range, List.range.loop, sealFrameSatP, sealFrameSat, sealSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Proof.AesGcm.preparedPowers8Repr_of_zeroMem fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem sealPrepared_framed (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn))
      (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576) :=
  AArch64.Verified.stackArgScratch (sig := Proof.Gcm.sealPrepared8Sig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealPrepared8Pre AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2576)
    (sealPrepared_verified v gp hMK) (by decide) (by decide) (Proof.AesGcm.sealPrepared8Pre_local _)
    (Proof.AesGcm.sealPrepared8Post_local _) sealFrameSatP_pre

end VG.Proof.AesGcm.AArch64.Fast
