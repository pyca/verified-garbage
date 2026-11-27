module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.CrtResult

/-! ### `Bignum.Arm.CrtAcceptedFactors`, which this module and modules that import it used -/

section

/-! # Accepted factors are safe odd moduli for both private powers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.accepted_factors {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (accepted : crtAccepted bs) :
    (1 < Spec.Rsa.os2ip (bs 2) ∧ Spec.Rsa.os2ip (bs 2) % 2 = 1) ∧
    (1 < Spec.Rsa.os2ip (bs 3) ∧ Spec.Rsa.os2ip (bs 3) % 2 = 1) := by
  have plen := (h.buffers.source 2).length
  have qlen := (h.buffers.source 3).length
  obtain ⟨odd, _, pSmall, qSmall⟩ := crt_bounds_of h.valid h.buffers.lengthValid.1
    plen h.buffers.pShort qlen h.buffers.qShort
  exact ⟨factor_facts (by rw [Nat.mul_comm]; exact accepted.2.2) qSmall odd,
    factor_facts accepted.2.2 pSmall odd⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtPowerStage`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtSharedPowerSources`, which this module and modules that import it used -/

section

/-! # Recover ciphertext and exponent arguments in either selected factor workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.power_sources {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s) (i : Fin 6) (exponent : i = 3 ∨ i = 4)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    CrtPowerSources child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  refine ⟨⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide),
    h.stack.read (by have := i.isLt; omega_using []), h.stack.read (by have := i.isLt; omega_using [])⟩, h.stack.separate.sub_right sub, by have := i.isLt; omega_using [],
    h.stack.pointer 0, h.stack.count, h.stack.pointer i, ?_⟩,
    h.buffers.source 1, h.buffers.source i.succ, (h.buffers.sourceSeparate 1).sub_right sub,
    (h.buffers.sourceSeparate i.succ).sub_right sub,
    by have := h.buffers.lengthValid.1; omega_using [this], (crt_width_valid h.buffers.lengthValid).2.2, ?_, ?_⟩
  · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega_using []] using h.stack.length i
  · rcases exponent with rfl | rfl
    · exact h.buffers.pPositive
    · exact h.buffers.qPositive
  · have length := h.buffers.lengthValid.2
    rcases exponent with rfl | rfl
    · change g.pLength < _; have := h.buffers.pShort; omega_using [length, this]
    · change g.qLength < _; have := h.buffers.qShort; omega_using [length, this]

end VG.Proof.Bignum.Arm

end

end

/-! # Select a factor, compute its private power, and restore the main workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_powerStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (kind : CrtChild g child slot) (j i : Fin 6) (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4))
    (bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1)
    (valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < numAt s.mem (State.addr child) g.words 0 ∧ numAt s.mem (State.addr child) g.words 0 % 2 = 1)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ))
    (st : CrtStages) (hst : st.ok g bs) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.powerOf st.prime kernel.code slot (56 + 8 * j.val) (56 + 8 * i.val) kernel.mul.op) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
        FrameStack.belowA s.sp 48] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨member, ws, layout, _, slotFit, slotSmall, link⟩ := h.child kind
  have exponent : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  rw [CrtFn.powerOf, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h ws layout member slotFit slotSmall ready.ptr link) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have eqU := h.workspace_eq_after_base ws member frameU
  have flagU := acceptance_after_base_save frameU restU
  have modulusU := eqU.number h.buffers.context.arraysFit (by decide : 0 < 8)
  have input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) u :=
    ⟨⟨readyU, by have := sharedU.stack.nowrap; omega_using [this], sharedU.stack.read (by decide),
      by rw [flagU]; exact bit, by rw [flagU, modulusU]; exact valid⟩,
      sharedU.power_sources i exponent member⟩
  rw [WP.seq_iff]
  refine WP.mono ((crt_narrowPower_ok (kernel := kernel)) u sharedU kind j i pair input (by rw [modulusU]; exact prime) st hst) ?_
  rintro v ⟨sharedV, powered, flagV, frameV, restV⟩
  rw [flagU, modulusU] at powered
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eqT := sharedV.workspace_eq_after_base (sharedV.child kind).2.1 member frameT
  have flag := (acceptance_after_base_save frameT restT).trans (flagV.trans flagU)
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restU.sp] at frameV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, powered.congr eqT, flag,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans (frameT.mono (by simp))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm

end

end

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
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem) :
    WorkspaceEq (State.addr other) (8 * workspaceWords g.words) s.mem t.mem := by
  apply h.eq_of_frame ws member (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩,
    ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, FrameStack.belowA s.sp 48])
    (frame.mono (by simp))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sep
  · exact sepN
  · exact h.stack.below.symm.sub_left (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member)

theorem CrtShared.live_after_power {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩,
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem) :
    Frame (crtLiveMutable g s.sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member⟩
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits h.narrow_member⟩
  · exact ⟨⟨State.addr s.sp, 4⟩, by simp [crtLiveMutable], fun _ h => h⟩
  · exact ⟨FrameStack.belowA s.sp 48, by simp [crtLiveMutable], fun _ h => h⟩

theorem crt_bothPowers_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2))
    (q : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3))
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0))
    (st : CrtStages) (hst : st.ok g bs) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (.seq (CrtFn.powerOf st.prime kernel.code 224 64 80 kernel.mul.op) (CrtFn.powerOf st.prime kernel.code 228 72 88 kernel.mul.op)) s fun t =>
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
  refine WP.mono ((crt_powerStage_ok (kernel := kernel)) s h ready (Or.inl ⟨rfl, rfl⟩) 1 3 (Or.inl ⟨rfl, rfl⟩) bit validP p st hst) ?_
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
    (by rw [flagU]; exact bit) validQ qU st hst) ?_
  rintro t ⟨sharedT, readyT, poweredQ, flagT, frameT, restT⟩
  rw [flagU, flag, qU, crt_safeFactor] at poweredQ
  have pEq := sharedU.workspace_eq_after_power sharedU.buffers.context.p (by simp [crtRegions])
    sharedU.buffers.context.sepPQ sharedU.buffers.context.sepPN frameT
  have frameTLive := sharedU.live_after_power (by simp [crtRegions]) frameT
  rw [restU.sp] at frameTLive
  exact ⟨sharedT, readyT, poweredP.congr pEq, poweredQ, flagT.trans (flagU.trans flag),
    (h.live_after_power (by simp [crtRegions]) frameU).trans frameTLive, restU.trans restT⟩

end VG.Proof.Bignum.Arm
