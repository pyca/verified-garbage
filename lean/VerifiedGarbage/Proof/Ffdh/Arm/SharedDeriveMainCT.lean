module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveTailCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt

/-! The derivation branches only on the scalar's validity, which its status discloses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt Operand arrAt)

structure MainInput (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  calls : SharedExchange.CallMemory p xb.length s
  scalar : Octets p.base p.privateValue p.len xb s
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩
  output : OutputBuffer p.output p.k s
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩

structure Imported (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop extends
    Prepared p slots xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip xb

structure Ranged (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop extends
    Prepared p slots xb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip xb)

theorem prepare_ready (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : MainInput p slots xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (Prepared p slots xb) := by
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h.context h.calls.toDomainCallMemory stable h0 h24 h32
    large odd normalized) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  refine ⟨context, ready, modulus, r2, h.calls.after rest, h.scalar.after_frame frame rest ?_,
    h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩
  intro r hr
  simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact h.scalar.separate
  · exact h.scalarStack.sub_right (Offset.sub_base _ (by decide))
  · exact h.scalarStack.sub_right (Offset.sub_base _ (by decide))
  · exact h.calls.scalarBelow

theorem import_ready (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Prepared p slots xb s) (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (positive : 0 < xb.length) (length : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (Imported p slots xb) := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    positive (Nat.le_trans length p.width.2.2.2.1) count) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.calls.after rest,
    h.scalar.after_workspace frame rest, h.output.after rest, h.workspaceSep,
    by rw [rest.sp]; exact h.stackSep⟩, value⟩

theorem range_ready (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Imported p slots xb s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (Ranged p slots xb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro u ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.calls.after rest, h.scalar.after_workspace frame rest, h.output.after rest, h.workspaceSep,
    by rw [rest.sp]; exact h.stackSep⟩, flag⟩

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (h60 : 60 ∈ slots) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p))
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have fits : xb1.length < 2 ^ 32 := by have := p.maxLength; omega
  have prepare := (domainNormalizedPrepareAt24_ct backend stable h0 h24 h32 large odd normalized).mono
    (P' := fun (s t : State) => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.calls.toDomainCallMemory⟩,
      ⟨h.2.1.context, h.2.1.calls.toDomainCallMemory⟩, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (k := xb1.length)
    stable h40 h44 count (by decide)).mono
    (P' := fun (s t : State) => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable h28 h32 h60 odd).mono
    (P' := fun (s t : State) => Imported p slots xb1 s ∧ Imported p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩)
    (fun _ _ h => h)
  have branches : RelCT isa (fun s t => Ranged p slots xb1 s ∧ Ranged p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (VG.Impl.Ffdh.Arm.SharedDerive.tail (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        VG.Impl.Ffdh.Arm.SharedDerive.fail) (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p))
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq, ← classification] using h.flag)
      (fun _ _ h mem rest => ⟨h.toPrepared.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩)
      (fun _ _ h mem rest => ⟨h.toPrepared.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩)
    · intro _
      exact (tail_ct backend stable h4 h32 h40 h44 h56 saved positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toPrepared, h.2.1.toPrepared, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (fail_ct h4 h32).mono
        (fun _ _ h => ⟨h.1.toPrepared, h.2.1.toPrepared, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedDerive.main
  exact relCT_chain prepare
    (fun s h => prepare_ready backend s h stable h0 h24 h32 large odd normalized)
    (fun s h => prepare_ready backend s h stable h0 h24 h32 large odd normalized)
    (relCT_chain imports (fun s h => import_ready s h stable h40 h44 positive scalarLength count)
      (fun s h => import_ready s h stable h40 h44 (by rw [← length]; exact positive)
        (by rw [← length]; exact scalarLength) (by rw [← length]; exact count))
      (relCT_chain ranges (fun s h => range_ready s h stable h28 h32 h60 odd)
        (fun s h => range_ready s h stable h28 h32 h60 odd) branches))

end VG.Proof.Ffdh.Arm.SharedDerive
