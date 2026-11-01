module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the frame's push, the
entry, the loads of the call's arguments and of the return address are at
the stack pointer or our frame; the gathering is constant time by
`gather_rel` (`Proof/Gather/PPC64LE/LoopCT.lean`); and the call is constant
time by its callee's contract, whose public arguments agree
(`sealGather_ct`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/CT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint ct_of gather_rel)

theorem entered_desc {σ₁ σ₂ e₁ e₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂)
    (hq : gatherPub σ₁ σ₂) (he₁ : Entered σ₁ e₁) (he₂ : Entered σ₂ e₂) :
    ∀ j<Cnt σ₁*16,e₁.mem (Src σ₁+BitVec.ofNat 64 j)=e₂.mem (Src σ₁+BitVec.ofNat 64 j) := by
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  intro j hj
  have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ hj (by have := h₁.ods; omega)
  have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
    simp only [dsR, Src, Cnt, ← q9, ← q10]; exact hx
  rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
  exact hdesc j hj

theorem body_rel (hv : SealOk)
    (hct : ConstantTime isa (Spec.Gcm.sealContract PPC64LE.abi 2672).pre
      (Spec.Gcm.sealContract PPC64LE.abi 2672).pub sealCode)
    {σ₁ σ₂ e₁ e₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hq : gatherPub σ₁ σ₂)
    (he₁ : Entered σ₁ e₁) (he₂ : Entered σ₂ e₂) :
    RelCT isa (Eq2 e₁ e₂) body TT := by
  unfold body
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  have hP : Pf σ₁=Pf σ₂ := by simp only [Pf,Bs,qsp]
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q9, ← q10, ← a0, ← a1] at g₂
  have hd := entered_desc h₁ h₂ ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ he₁ he₂
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hP])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [.r12] (by rw [hg₁.sp, hg₂.sp, hP]) (by simp [hg₁.r12, hg₂.r12, hP])
    (by taint_decide)) (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, cR, nR, aR, C, Nn, NL, Ad, AL, aOut, Pf, Bs, q3, q5, q6, q7, q8, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, r9₁, r10₁⟩ := hc₁.callGpr
  obtain ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call hv hct (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r3₁, r4₁, r5₁, r6₁, r7₁,
        r8₁, r9₁, r10₁, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂, hc₁.sp, hc₂.sp, hP, hc₁.arg h₁, hc₂.arg h₂, C, Nn,
        Ad, Dst, Tg, q3, q4, q5, q6, q7, q8, a0, a1, a2, and_self])
    (called_wp hv h₁ hc₁) (called_wp hv h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide)


theorem sealGather_ct (hv : SealOk)
    (hct : ConstantTime isa (Spec.Gcm.sealContract PPC64LE.abi 2672).pre
      (Spec.Gcm.sealContract PPC64LE.abi 2672).pub sealCode) :
    ConstantTime isa gatherPre gatherPub sealGather := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, hdesc⟩ := hq
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, Bs, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 160 σ₁) (allocated 160 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show σ₁.sp - BitVec.ofNat 64 160 = σ₂.sp - BitVec.ofNat 64 160 by rw [qsp]) (by simp)
    (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  exact body_rel hv hct h₁ h₂ ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ he₁ he₂

end VG.Proof.AesGcm.PPC64LE.Gather
