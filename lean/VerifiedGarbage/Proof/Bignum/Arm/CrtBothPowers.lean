module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Block

/-! # Both private exponentiations retain their completed arithmetic states -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtFactor (bs : Fin 7 → List Byte) (i : Fin 7) : Nat :=
  if crtAccepted bs then Spec.Rsa.os2ip (bs i) else 3

theorem crt_safeFactor (bs : Fin 7 → List Byte) (i : Fin 7) :
    safePrime ((if crtAccepted bs then 1 else 0) : BitVec 32).toNat (Spec.Rsa.os2ip (bs i)) = crtFactor bs i := by
  by_cases accepted : crtAccepted bs <;> simp [safePrime, crtFactor, accepted]

theorem CrtShared.workspace_eq_after_power {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {child other : BitVec 32} (h : CrtShared g bs s)
    (ws : Workspace s other (8 * workspaceWords g.words))
    (member : (⟨State.addr other, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (sep : Region.Disjoint ⟨State.addr other, 8 * workspaceWords g.words⟩ ⟨State.addr child, 8 * workspaceWords g.words⟩)
    (sepN : Region.Disjoint ⟨State.addr other, 8 * workspaceWords g.words⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩,
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem) :
    WorkspaceEq (State.addr other) (8 * workspaceWords g.words) s.mem t.mem := by
  apply h.eq_of_frame ws member (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩,
    ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frame.mono (by simp))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sep
  · exact sepN

theorem CrtShared.live_after_power {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩,
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem) :
    Frame (crtLiveMutable g s.sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member⟩
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits h.narrow_member⟩
  · exact ⟨⟨State.addr s.sp, 4⟩, by simp [crtLiveMutable], fun _ h => h⟩

theorem crt_bothPowers_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2))
    (q : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3))
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (.seq ((CrtFn.powerWith kernel.code) 224 64 80) ((CrtFn.powerWith kernel.code) 228 72 88)) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 2)
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2)) t.mem ∧
      CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 3)
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 5)) (crtFactor bs 3)) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1 := by
    rw [flag]; split <;> decide
  have validP : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 % 2 = 1 := by
    rw [flag, p]
    by_cases accepted : crtAccepted bs
    · intro _; exact (h.accepted_factors accepted).1
    · simp [accepted]
  rw [WP.seq_iff]
  refine WP.mono ((crt_powerStage_ok (kernel := kernel)) s h ready (Or.inl ⟨rfl, rfl⟩) 1 3 (Or.inl ⟨rfl, rfl⟩) bit validP p) ?_
  rintro u ⟨sharedU, readyU, poweredP, flagU, frameU, restU⟩
  rw [flag, p, crt_safeFactor] at poweredP
  have qEq := h.workspace_eq_after_power h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepPQ.symm
    h.buffers.context.sepQN frameU
  have qU := (qEq.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans q
  have validQ : (u.mem.readW (off (State.addr u.sp) 48) 32).toNat ≠ 0 →
      1 < numAt u.mem (State.addr (crtQ g.base g.words)) g.words 0 ∧
      numAt u.mem (State.addr (crtQ g.base g.words)) g.words 0 % 2 = 1 := by
    rw [flagU, flag, qU]
    by_cases accepted : crtAccepted bs
    · intro _; exact (h.accepted_factors accepted).2
    · simp [accepted]
  refine WP.mono ((crt_powerStage_ok (kernel := kernel)) u sharedU readyU (Or.inr ⟨rfl, rfl⟩) 2 4 (Or.inr ⟨rfl, rfl⟩)
    (by rw [flagU]; exact bit) validQ qU) ?_
  rintro t ⟨sharedT, readyT, poweredQ, flagT, frameT, restT⟩
  rw [flagU, flag, qU, crt_safeFactor] at poweredQ
  have pEq := sharedU.workspace_eq_after_power sharedU.buffers.context.p (by simp [crtRegions])
    sharedU.buffers.context.sepPQ sharedU.buffers.context.sepPN frameT
  have frameTLive := sharedU.live_after_power (by simp [crtRegions]) frameT
  rw [restU.sp] at frameTLive
  exact ⟨sharedT, readyT, poweredP.congr pEq, poweredQ, flagT.trans (flagU.trans flag),
    (h.live_after_power (by simp [crtRegions]) frameU).trans frameTLive, restU.trans restT⟩

end VG.Proof.Bignum.Arm
