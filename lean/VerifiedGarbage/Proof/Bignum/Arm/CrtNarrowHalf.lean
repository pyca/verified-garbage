module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.TransferPadded
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Block

/-! # A full-width number modulo the narrow workspace's modulus

A number `x` of `w ≤ 2 v` limbs is `l + h R` with `R = 2^(64 v)` and `l`, `h`
below `R`: `h R mod M` from `h R² R⁻¹`, its negation from zero, and `l mod M`
from `l R² R⁻¹ R⁻¹` give `x mod M = l mod M - (0 - h R mod M)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

/-- `l mod M - (0 - c mod M)`, modulo `M`, is `l + c`. -/
theorem half_combine {M l c : Nat} (pos : 0 < M) :
    (l % M + M - (0 + M - c % M) % M) % M = (l + c) % M := by
  have hc := Nat.mod_lt c pos
  rw [Nat.zero_add]
  rcases Nat.eq_zero_or_pos (c % M) with zero | positive
  · rw [zero, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod, Nat.add_mod l c, zero,
      Nat.add_zero, Nat.mod_mod]
  · rw [Nat.mod_eq_of_lt (by omega_using [pos, positive] : M - c % M < M), show l % M + M - (M - c % M) = l % M + c % M by omega_using [hc],
      ← Nat.add_mod]

/-- A cleared array is zero. -/
theorem numAt_of_cleared {m : Mem} {base : Addr} {w o : Nat}
    (cleared : val32 m base (arrAt w o) (2 * w + 2) = 0) : numAt m base w o = 0 := by
  rw [numAt_native]; exact (val32_zero_split cleared).1

theorem CrtCopyCtx.after_narrow {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} {rs : List Reg} (h : CrtCopyCtx g bs child slot v s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem)
    (rest : Rest rs s t) : CrtCopyCtx g bs child slot v t := by
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  have sepM : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.shared.buffers.context.sepMN
  have frame' : Frame (⟨State.addr s.sp, 4⟩ :: [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩])
      s.mem t.mem := frame.mono (by simp)
  have eqC := h.shared.eq_of_frame h.childWs h.member frame' sepN
  have eqM := h.shared.eq_of_frame h.shared.buffers.context.main (by simp [crtRegions]) frame' sepM
  exact ⟨h.shared.after_narrow (frame.mono (by simp)) rest, ready, h.childWs.congr rest.wr, h.member,
    h.layout.congr eqC, h.sep, h.slotFit, h.slotSmall,
    by rw [eqM.word (d := slot) (bits := 32) (by have := h.slotFit; omega_using [this])]; exact h.link, h.le⟩

theorem CrtShared.copyCtx {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} (h : CrtShared g bs s) (kind : CrtChild g child slot)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) (le : v ≤ g.words) :
    CrtCopyCtx g bs child slot v s :=
  ⟨h, ready, (h.child kind).2.1, (h.child kind).1, (h.child kind).2.2.1, (h.child kind).2.2.2.1,
    (h.child kind).2.2.2.2.1, (h.child kind).2.2.2.2.2.1, (h.child kind).2.2.2.2.2.2, le⟩

theorem CrtCopyCtx.child_num {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem) :
    numAt t.mem (State.addr child) g.words j = numAt s.mem (State.addr child) g.words j := by
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  have eqC := h.shared.eq_of_frame h.childWs h.member (frame.mono (by simp)) sepN
  exact eqC.number (h.layout.width ▸ h.layout.layout.2.2.1) hj

theorem CrtCopyCtx.child_eq {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} (h : CrtCopyCtx g bs child slot v s)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem) :
    WorkspaceEq (State.addr child) (8 * workspaceWords g.words) s.mem t.mem := by
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  exact h.shared.eq_of_frame h.childWs h.member (frame.mono (by simp)) sepN

/-- After a copy into the low limbs of the full array `j`: the context holds, the
narrow workspace is unchanged and the full one keeps its other arrays. -/
theorem CrtCopyCtx.after_copyOut {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (kind : CrtChild g child slot) (hj : j < 8)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (outside : Outside (State.addr child) (arrAt g.words j) (8 * v) s.mem t.mem) (rest : Rest roundClobbers s t) :
    CrtCopyCtx g bs child slot v t ∧ Keeps (State.addr child) (workspaceWords g.words) g.words j s.mem t.mem ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      WorkspaceEq (State.addr (crtN g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem := by
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.layout.width ▸ h.layout.layout.2.2.1
  have endJ := Nat.le_trans (array_end_le (w := g.words) hj) fitsC
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by simp only [workspaceWords]; omega_using [words]
  have le := h.le
  have frameC := outside_workspace outside (size := 8 * workspaceWords g.words) (by omega_using [endJ, le])
  have keeps := outside_array_prefix_keeps outside (by omega_using [wsSmall] : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_using [le] : 8 * v ≤ 8 * (g.words + 2))
  have layoutT : CrtLayoutState child (workspaceWords g.words) g.words t.mem := by
    have kl := keeps_layout h.layout.layout (by rw [h.layout.width]; exact keeps)
    exact ⟨kl.2, kl.1.trans h.layout.width⟩
  have sharedT : CrtShared g bs t := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem :=
      frameC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.shared.after_p f rest layoutT
    · exact h.shared.after_q f rest layoutT
  have sepC : ∀ r ∈ [(⟨State.addr child, 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep.symm
  have eqN := h.shared.eq_of_frame h.shared.buffers.context.narrow h.shared.narrow_member
    (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩]) (frameC.mono (by simp)) sepC
  exact ⟨⟨sharedT, ready, (sharedT.child kind).2.1, h.member, layoutT, h.sep, h.slotFit, h.slotSmall,
    (sharedT.child kind).2.2.2.2.2.2, h.le⟩, keeps, frameC, eqN⟩

theorem crt_reduceHalf_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j M : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) (half : g.words ≤ 2 * v)
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M) :
    WP isa (reduceHalf slot j) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 7 = 1 ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 1 = numAt s.mem (State.addr child) g.words j % M ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.ready.width ▸ h.ready.layout.2.2.1
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have positive : 0 < M := by have := h.ready.modulus; omega_using [odd]
  -- `h`, the high limbs, into array 1.
  rw [reduceHalf, WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s h.ready (o := 1) (by decide) (by decide)) ?_
  rintro s1 ⟨ready1, cleared1, keeps1, frame1, rest1⟩
  have ctx1 := h.after_narrow ready1 frame1 rest1
  have mod1 := (keeps_array_num keeps1 fits (op 0 (by simp)) (by decide)).trans modulus
  have r21 := (keeps_array_num keeps1 fits (op 4 (by simp)) (by decide)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (crt_copyHigh_ok s1 ctx1 hj (by decide) (by decide) half) ?_
  rintro s2 ⟨ready2, high2, keeps2, frame2, rest2⟩
  replace high2 := high2 cleared1
  rw [h.child_num hj frame1] at high2
  have mod2 := (keeps_array_num keeps2 fits (op 0 (by simp)) (by decide)).trans mod1
  have r22 := (keeps_array_num keeps2 fits (op 4 (by simp)) (by decide)).trans r21
  -- One, and `h R mod M`.
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s2 (o := 7) 1 ready2 (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s3 ⟨ready3, one3, _, keeps3, frame3, rest3⟩
  have mod3 := (keeps_array_num keeps3 fits (op 0 (by simp)) (by decide)).trans mod2
  have r23 := (keeps_array_num keeps3 fits (op 4 (by simp)) (by decide)).trans r22
  have high3 := (keeps_array_num keeps3 fits (op 1 (by simp)) (by decide)).trans high2
  rw [WP.seq_iff]
  refine WP.mono (montEncode_ok s3 ready3 (op 1 (by simp)) (op 1 (by simp)) (by decide) mod3 odd r23) ?_
  rintro s4 ⟨ready4, mod4, enc4, keeps4, frame4, rest4⟩
  rw [high3] at enc4
  have r24 := (keeps_array_num keeps4 fits (op 4 (by simp)) (by decide)).trans r23
  have one4 := (keeps_array_num keeps4 fits (op 7 (by simp)) (by decide)).trans one3
  -- Its negation, from a zero array 5, into array 6.
  rw [WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s4 ready4 (o := 5) (by decide) (by decide)) ?_
  rintro s5 ⟨ready5, cleared5, keeps5, frame5, rest5⟩
  have mod5 := (keeps_array_num keeps5 fits (op 0 (by simp)) (by decide)).trans mod4
  have r25 := (keeps_array_num keeps5 fits (op 4 (by simp)) (by decide)).trans r24
  have one5 := (keeps_array_num keeps5 fits (op 7 (by simp)) (by decide)).trans one4
  have enc5 := (keeps_array_num keeps5 fits (op 1 (by simp)) (by decide)).trans enc4
  have zero5 : numAt s5.mem (State.addr (crtN g.base g.words)) v 5 = 0 := numAt_of_cleared cleared5
  rw [WP.seq_iff]
  refine WP.mono (subModArray_ok s5 ready5 (o := 6) (a := 5) (b := 1) (op 6 (by simp)) (op 5 (by simp))
    (op 1 (by simp)) (by decide) (by decide) (by decide) (by rw [zero5, mod5]; exact positive)
    (by rw [enc5, mod5]; exact Nat.mod_lt _ positive)) ?_
  rintro s6 ⟨ready6, neg6, keeps6, frame6, rest6⟩
  rw [zero5, mod5, enc5] at neg6
  have mod6 := (keeps_array_num keeps6 fits (op 0 (by simp)) (by decide)).trans mod5
  have r26 := (keeps_array_num keeps6 fits (op 4 (by simp)) (by decide)).trans r25
  have one6 := (keeps_array_num keeps6 fits (op 7 (by simp)) (by decide)).trans one5
  -- `l mod M`, from the low limbs into array 5.
  have frame16 : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s1.mem s6.mem :=
    frame2.trans (frame3.trans (frame4.trans (frame5.trans frame6)))
  have rest16 : Rest roundClobbers s1 s6 := rest2.trans (rest3.trans (rest4.trans (rest5.trans rest6)))
  have ctx6 := ctx1.after_narrow ready6 frame16 rest16
  rw [WP.seq_iff]
  refine WP.mono (crt_copyLow_ok s6 ctx6 hj (by decide) (by decide)) ?_
  rintro s7 ⟨ready7, low7, keeps7, frame7, rest7⟩
  rw [ctx1.child_num hj frame16, h.child_num hj frame1] at low7
  have mod7 := (keeps_array_num keeps7 fits (op 0 (by simp)) (by decide)).trans mod6
  have r27 := (keeps_array_num keeps7 fits (op 4 (by simp)) (by decide)).trans r26
  have one7 := (keeps_array_num keeps7 fits (op 7 (by simp)) (by decide)).trans one6
  have neg7 := (keeps_array_num keeps7 fits (op 6 (by simp)) (by decide)).trans neg6
  rw [WP.seq_iff]
  refine WP.mono (reduceOperand_ok s7 ready7 (op 5 (by simp)) (by decide) (by decide) mod7 odd r27 one7) ?_
  rintro s8 ⟨ready8, mod8, low8, keeps8, frame8, rest8⟩
  rw [low7] at low8
  have r28 := (keeps_array_num keeps8 fits (op 4 (by simp)) (by decide)).trans r27
  have one8 := (keeps_array_num keeps8 fits (op 7 (by simp)) (by decide)).trans one7
  have neg8 := (keeps_array_num keeps8 fits (op 6 (by simp)) (by decide)).trans neg7
  -- The difference.
  refine WP.mono (subModArray_ok s8 ready8 (o := 1) (a := 5) (b := 6) (op 1 (by simp)) (op 5 (by simp))
    (op 6 (by simp)) (by decide) (by decide) (by decide) (by rw [low8, mod8]; exact Nat.mod_lt _ positive)
    (by rw [neg8, mod8]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨readyT, valueT, keepsT, frameT, restT⟩
  refine ⟨readyT, (keeps_array_num keepsT fits (op 0 (by simp)) (by decide)).trans mod8,
    (keeps_array_num keepsT fits (op 4 (by simp)) (by decide)).trans r28,
    (keeps_array_num keepsT fits (op 7 (by simp)) (by decide)).trans one8, ?_,
    frame1.trans (frame16.trans (frame7.trans (frame8.trans frameT))),
    rest1.trans (rest16.trans (rest7.trans (rest8.trans restT)))⟩
  rw [valueT, low8, mod8, neg8, half_combine positive, Nat.mod_add_div']

end VG.Proof.Bignum.Arm
