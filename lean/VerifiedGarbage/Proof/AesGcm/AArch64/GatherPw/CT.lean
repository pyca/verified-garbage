module
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Contract

import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
meta import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Callee
meta import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM out of place from a list of slices, with the powers, AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace, as for
`vg_aes_gcm_seal_gather` (`Gather/CT.lean`): the entry, the loads of the
call's arguments and of the return address are at the stack pointer; the
gathering is constant time by `gather_rel` (`LoopCT.lean`); and the call is
constant time by its callee's contract, whose public arguments, `pw` among
them, agree (`sealGatherPw_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.GatherPw

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of)
open VG.Proof.AesGcm.AArch64.Gather (K Nn NL Ad AL Src Cnt Dst L Tg nR aR dsR lsR dR tgR gather_rel)

theorem sealGatherPw_ct (F : SealPwFn) :
    ConstantTime isa gatherAArch64.pre gatherPub (sealGatherPw F.fn) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁.1
  have h₂ := lay p₂.1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, a1, a2, a3, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 32 σ₁) (allocated 32 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (by rw [allocated_sp h₁, allocated_sp h₂, hB]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q6, ← q7, ← a0, ← a1] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega)
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q6, ← q7]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hB])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [] (by rw [hg₁.sp, hg₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, ctxR, nR, aR, pwR, Pw, K, Nn, NL, Ad, AL, q0, q2, q3, q4, q5, a3, hB]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁⟩ := hc₁.callGpr
  obtain ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂⟩ := hc₂.callGpr
  obtain ⟨t0₁, t1₁⟩ := hc₁.stackArgs h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨t0₂, t1₂⟩ := hc₂.stackArgs h₂ (rdC σ₁) (wrC σ₁)
  have i₁ : Spec.Gcm.Powers8Repr (c₁.callEntry.withRegions (rdC σ₁) (wrC σ₁)).mem
      (stackArg (c₁.callEntry.withRegions (rdC σ₁) (wrC σ₁)) 1)
      (Spec.Gcm.ctxH (c₁.callEntry.withRegions (rdC σ₁) (wrC σ₁)).mem
        ((c₁.callEntry.withRegions (rdC σ₁) (wrC σ₁)).gpr .x0)) := by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, r0₁, t1₁, hc₁.mem]
    exact powers_gMem h₁ p₁.2
  have i₂ : Spec.Gcm.Powers8Repr (c₂.callEntry.withRegions (rdC σ₁) (wrC σ₁)).mem
      (stackArg (c₂.callEntry.withRegions (rdC σ₁) (wrC σ₁)) 1)
      (Spec.Gcm.ctxH (c₂.callEntry.withRegions (rdC σ₁) (wrC σ₁)).mem
        ((c₂.callEntry.withRegions (rdC σ₁) (wrC σ₁)).gpr .x0)) := by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, r0₂, t1₂, hc₂.mem]
    exact powers_gMem h₂ p₂.2
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨F.pre _ cp₁ i₁, F.pre _ cp₂ i₂, F.pub _ _ ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r0₁, r1₁, r2₁, r3₁, r4₁, r5₁,
        r6₁, r7₁, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂, hc₁.sp, hc₂.sp, hB, t0₁, t1₁, t0₂, t1₂, q0, q1, q2,
        q3, q4, q5, Dst, Tg, Pw, a0, a1, a2, a3, and_self])
    (called_wp F h₁ p₁.2 hc₁) (called_wp F h₂ p₂.2 hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64.GatherPw
