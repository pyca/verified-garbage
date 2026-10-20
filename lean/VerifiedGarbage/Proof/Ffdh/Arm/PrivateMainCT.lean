module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMain
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePublicCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset

/-! Imported private-key validation branches on the scalar validity class disclosed by its status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand arrAt)

structure PrivateMainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩

structure PrivateScalarImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip xb

structure PrivateScalarRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip xb)

theorem PrivateScalarRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateScalarRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateScalarRanged p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privatePrepare_ready (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateMainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (PrivateReady p slots yb xb) := by
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ prepareAtWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
  exact ⟨context, ready, modulus, r2, h.value.after_frame frame rest (sourceSep h.value h.valueStack),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack)⟩

theorem privateImport_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (positive : 0 < xb.length) (length : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (PrivateScalarImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    positive (Nat.le_trans length p.width.2.2.2.1) count) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, value⟩

theorem privateRange_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateScalarImported p slots yb xb s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (PrivateScalarRanged p slots yb xb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro u ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, flag⟩

theorem privateMain_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p))
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main (fun _ _ => True) := by
  have pStack (s : State) {xb : List Byte} (h : PrivateMainInput p slots yb xb s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  have prepare := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.context, h.1.context.pBytes, pStack s h.1⟩,
      ⟨h.2.1.context, h.2.1.context.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (k := xb1.length)
    stable h40 h44 count (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable h28 h32 h60 odd).mono
    (P' := fun (s t : State) => PrivateScalarImported p slots yb xb1 s ∧ PrivateScalarImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => PrivateScalarRanged p slots yb xb1 s ∧ PrivateScalarRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck (VG.Impl.Ffdh.Arm.Domain.ret 2))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p))
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq, ← classification] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (privatePublic_ct stable h28 h32 h36 h40 h44 h56 h60 peerLength positive
        (by have := p.maxLength; omega) count length odd).mono
        (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main
  exact relCT_chain prepare (fun s h => privatePrepare_ready s h stable h0 h24 h32 large odd)
    (fun s h => privatePrepare_ready s h stable h0 h24 h32 large odd)
    (relCT_chain imports (fun s h => privateImport_scalar s h stable h40 h44 positive scalarLength count)
      (fun s h => privateImport_scalar s h stable h40 h44 (by rw [← length]; exact positive)
        (by rw [← length]; exact scalarLength) (by rw [← length]; exact count))
      (relCT_chain ranges (fun s h => privateRange_scalar s h stable h28 h32 h60 odd)
        (fun s h => privateRange_scalar s h stable h28 h32 h60 odd) branches))

end VG.Proof.Ffdh.Arm
