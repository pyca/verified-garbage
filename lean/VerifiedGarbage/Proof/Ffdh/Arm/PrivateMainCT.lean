module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateState

import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMain
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
/-! Imported private-key validation branches on the scalar validity class disclosed by its status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateMatchCT.lean`, which only this module imported.
section

/-! Computing g^x and comparing it with the imported public value is constant time in x. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem privateMatch_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (fun _ _ => True) := by
  have powers := (powerAt_ct (p := p) (bs := 56) (es := 40) (ec := 44)
    stable h56 h40 h44 h32 p.gLength positive fits count length odd).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.context.gBytes, h.1.scalar⟩,
      ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.context.gBytes, h.2.1.scalar⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPower (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s)
      (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 56 40 44) s (PrivateReady p slots yb xb) := by
    refine WP.mono (powerAt_ok s 56 40 44 h.context stable h56 h40 h44 h32 h.ready h.modulus odd h.r2
      h.context.gBytes p.gLength h.scalar positive fits count) ?_
    rintro u ⟨context, ready, _, modulus, r2, _, frame, rest⟩
    exact ⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (ArithmeticReady p.base p.len p.w) :=
    WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
      (by rw [peerLength]; have := p.minLength; omega) (by rw [peerLength]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [peerLength])) fun _ j => j.2.1
  have equal := equal_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic
  exact relCT_chain powers (fun s h => wpPower s h positive fits count)
    (fun s h => wpPower s h (by rw [← length]; exact positive)
      (by rw [← length]; exact fits) (by rw [← length]; exact count))
    (relCT_chain imports (fun s h => wpImport s h) (fun s h => wpImport s h) (equal.seq finishFlag_ct))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateTailCT.lean`, which only this module imported.
section

/-! Private-key subgroup branches depend on the public value, followed by constant-time consistency checking. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure PrivateMember (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then 1 else 0

theorem PrivateMember.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateMember p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateMember p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateTail_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => PrivateReady p slots yb xb s ∧ s.z = !p.hasQ
  have tests := qTest_ct.mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wpTest (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.qTest s (Q xb) := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have matchCT := privateMatch_ct stable h32 h36 h40 h44 h56 peerLength positive fits count length odd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36)
        (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0)))
        VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic) (fun _ _ => True) := by
    apply iteKnownPair_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
      (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      have subgroup := (subgroup_ct stable h36 h60 h32 hasQ peerLength odd).mono
        (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
        (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.value⟩,
          ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.value⟩, h.2.2⟩) (fun _ _ h => h)
      have wpSubgroup (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
          WP isa (VG.Impl.Ffdh.Arm.Domain.subgroup 36) s (PrivateMember p slots yb xb) := by
        refine WP.mono (subgroup_ok s 36 h.context stable h36 h60 h32 hasQ h.ready h.modulus odd h.r2 h.value peerLength) ?_
        rintro u ⟨context, ready, flag, modulus, r2, frame, rest⟩
        exact ⟨⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, flag⟩
      have matched : RelCT isa (fun s t => PrivateMember p slots yb xb1 s ∧ PrivateMember p slots yb xb2 t ∧ s.sp = t.sp)
          (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0))
          (fun _ _ => True) := by
        apply ifFlag_pair_ct (decide (Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1))
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
        · intro _
          exact matchCT.mono (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
        · intro _
          exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
      exact (relCT_chain subgroup (fun s h => wpSubgroup s h) (fun s h => wpSubgroup s h) matched).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact matchCT.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests (fun s h => wpTest s h) (fun s h => wpTest s h) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivatePublicCT.lean`, which only this module imported.
section

/-! The public half of private-key checking reveals no private scalar data. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure PrivateImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure PrivateRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem PrivateRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateRanged p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateImport_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true) (h36 : 36 ∈ slots) (h32 : 32 ∈ slots)
    (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (PrivateImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, value⟩

theorem privateRange_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateImported p slots yb xb s) (stable : stableSlots slots = true) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (PrivateRanged p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro u ⟨ready, flag, arrays, frame, rest⟩
  rw [h.imported, h.modulus] at flag
  exact ⟨h.toPrivateReady.after_workspace stable frame rest ready
    ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩

theorem privatePublic_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck (fun _ _ => True) := by
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1) (by decide)).mono
    (P' := fun (s t : State) => PrivateImported p slots yb xb1 s ∧ PrivateImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => PrivateRanged p slots yb xb1 s ∧ PrivateRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (privateTail_ct stable h28 h32 h36 h40 h44 h56 h60 peerLength positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck
  exact relCT_chain imports (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (relCT_chain ranges (fun s h => privateRange_public s h stable odd)
      (fun s h => privateRange_public s h stable odd) branches)

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

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
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
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
