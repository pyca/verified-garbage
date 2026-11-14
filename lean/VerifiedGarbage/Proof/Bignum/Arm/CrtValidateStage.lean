module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadQStage
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationPreserved
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValues
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
/-! # Exact acceptance and imported factors for the private RSA computation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductStage.lean`, which only this module imported.
section

/-! # Accumulate the exact factor-product validation bit -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- A number of `n` words below `2^(32 k)`, `k ≤ n`, is its first `k`. -/
theorem val32_prefix {m : Mem} {B : Addr} {d n k v : Nat} (hv : val32 m B d n = v) (hk : k ≤ n)
    (hlt : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have a := val32_append m B d k (n - k)
  rw [show k + (n - k) = n by omega, hv] at a
  have hpos := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (n - k)) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at a; exact a.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) h; omega

/-- The product stage, its product of `p`'s first `m` words by `q`'s first `n`
(`count`'s counts), which hold them. -/
theorem crt_productStageWith_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {count : List Instr}
    {m n : Nat} (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (hc : CountFrom count g.base g.size m n s) (hm : 0 < m) (hm' : m ≤ 2 * g.words) (hn : 0 < n)
    (hn' : n ≤ 2 * g.words)
    (fitP : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 < 2 ^ (32 * m))
    (fitQ : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 < 2 ^ (32 * n)) :
    WP isa (.seq (validateProductWith count) (.block mergeAcceptance)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 *
          numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0) then 1 else 0) &&&
        s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_validateProductWith_ok s (h.validate_input ready) hc hm hm' hn hn') ?_
  rintro u ⟨value, outside, frame, ptr, rest⟩
  have sharedU := h.after_validation outside frame rest
  have readyU : LayoutFrameReady g.base (workspaceWords g.words) g.words u :=
    ⟨⟨sharedU.buffers.context.main, sharedU.main.layout, sharedU.main.width, ptr⟩,
      by rw [rest.rd, rest.wr, rest.sp]; exact ready.stackRead,
      by rw [rest.sp]; exact ready.stackSep,
      saved_base_kept frame (h.stack.separate.sub_left (Region.sub_prefix (by decide))) ready.saved rest.sp⟩
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem u.mem := WorkspaceEq.of_frame (by decide) frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stack.separate)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact stackEq.word (by decide)
  obtain ⟨pEq, qEq⟩ := h.validation_child_eq outside
  obtain ⟨pValue, qValue⟩ := h.product_values false
  rw [val32_prefix pValue hm' fitP, val32_prefix qValue hn' fitQ, h.modulus] at value
  refine WP.mono (mergeAcceptanceLayout_ready u readyU (by have := sharedU.stack.nowrap; omega)
    (sharedU.stack.write (by decide))
    ((sharedU.stack.separate.symm.sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits
      (by simp [crtRegions]))).sub_right (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨readyT, flagT, _, frameT, restT, _⟩
  have separate : ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], (⟨State.addr g.base, g.size⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact sharedU.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))
  have sharedT := sharedU.after_external frameT restT (by simp [crtLiveMutable]) separate
  have eqChild (child : BitVec 32) (ws : Workspace u child (8 * workspaceWords g.words))
      (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
      WorkspaceEq (State.addr child) (8 * workspaceWords g.words) u.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frameT
      (fun r hr => (separate r hr).sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits member))
  rw [value, flagU] at flagT
  have frameTLive := frameT.mono (show ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], r ∈ crtLiveMutable g u.sp by simp [crtLiveMutable])
  rw [rest.sp] at frameTLive
  exact ⟨sharedT, readyT,
    ((eqChild _ sharedU.buffers.context.p (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (pEq.number h.buffers.context.arraysFit (by decide)),
    ((eqChild _ sharedU.buffers.context.q (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (qEq.number h.buffers.context.arraysFit (by decide)), flagT,
    (frame.mono (by simp [crtLiveMutable])).trans frameTLive,
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtAccepted (bs : Fin 7 → List Byte) : Prop :=
  Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) ∧
  Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) ∧
  Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)
instance (bs : Fin 7 → List Byte) : Decidable (crtAccepted bs) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The checks, with the product of `p`'s first `m` words by `q`'s first `n`
(`count`'s counts), which hold them. -/
theorem crt_validateStageWith_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {count : List Instr}
    {m n : Nat} (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (hc : ∀ x, CrtShared g bs x → CountFrom count g.base g.size m n x) (hm : 0 < m) (hm' : m ≤ 2 * g.words)
    (hn : 0 < n) (hn' : n ≤ 2 * g.words) (fitP : Spec.Rsa.os2ip (bs 2) < 2 ^ (32 * m))
    (fitQ : Spec.Rsa.os2ip (bs 3) < 2 ^ (32 * n)) :
    WP isa (CrtFn.validateWith (validateProductWith count)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.validateWith, WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro x ⟨sharedX, readyX, pX, qX, flagX, frameX, restX⟩
  refine WP.mono (crt_productStageWith_ok x sharedX readyX (hc x sharedX) hm hm' hn hn'
    (by rw [pX, pV]; exact fitP) (by rw [qX]; exact fitQ)) ?_
  rintro t ⟨sharedT, readyT, pT, qT, flagT, frameT, restT⟩
  rw [pX, pV, qX, flagX, flagV, flagU] at flagT
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagT]
    by_cases hx : Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) <;>
      by_cases hi : Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) <;>
      by_cases hp : Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0) <;>
      simp [crtAccepted, hx, hi, hp]
  rw [restU.sp] at frameV
  rw [restV.sp, restU.sp] at frameX
  rw [restX.sp, restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, pT.trans (pX.trans pV), qT.trans qX, flag,
    frameU.trans (frameV.trans (frameX.trans frameT)), restU.trans (restV.trans (restX.trans restT))⟩

/-- A factor of the CRT holds in the modulus's `2 W` words. -/
theorem crt_factor_fit {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) {i : Fin 7}
    (hi : g.sourceLength i < g.length) : Spec.Rsa.os2ip (bs i) < 2 ^ (32 * (2 * g.words)) := by
  have len := (h.buffers.source i).length
  have w := (crt_width_valid h.buffers.lengthValid).2.2
  have := VG.Proof.Bignum.os2ip_lt (bs i)
  rw [len, VG.Proof.Bignum.pow256_eq] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [CrtGeometry.words]; omega_using [hi, w]))

theorem crt_validateStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validate s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have two := (crt_width_valid h.buffers.lengthValid).1
  exact crt_validateStageWith_ok s h ready (fun x hx => countFrom_productCount
      (by have := hx.buffers.storageFits
          simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, stride,
            workspaceWords] at this
          omega_using [this])
      (hx.main.toCrtLayoutState.nativeCount hx.buffers.context.main))
    (by simp only [CrtGeometry.words] at two ⊢; omega_using [two]) (Nat.le_refl _)
    (by simp only [CrtGeometry.words] at two ⊢; omega_using [two]) (Nat.le_refl _)
    (crt_factor_fit h (i := 2) h.buffers.pShort) (crt_factor_fit h (i := 3) h.buffers.qShort)

/-- The key check without `p q = n` (`CrtFn.validateGiven`), for a key whose
factors' product is the modulus. -/
theorem crt_validateGivenStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (pq : Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0))
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq CrtFn.acceptInput (.seq CrtFn.loadP CrtFn.loadQ)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro t ⟨sharedT, readyT, pT, qT, flagT, frameT, restT⟩
  rw [flagV, flagU] at flagT
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagT]
    by_cases hx : Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) <;>
      by_cases hi : Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) <;>
      simp [crtAccepted, hx, hi, pq]
  rw [restU.sp] at frameV
  rw [restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, pT.trans pV, qT, flag,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩


end VG.Proof.Bignum.Arm
