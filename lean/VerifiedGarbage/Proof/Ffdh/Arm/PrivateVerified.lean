module

import VerifiedGarbage.Proof.Ffdh.Arm.PrivateCorrect
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateBody
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
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core

/-! ### `Ffdh.Arm.PrivateContractCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateMainCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateState`, which only this module used -/

section

/-! Shared arithmetic and input-buffer invariants of native private-key validation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure PrivateReady (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s

theorem PrivateReady.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : PrivateReady p slots yb xb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

theorem PrivateReady.after_workspace {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ready : ArithmeticReady p.base p.len p.w t) (modulus : numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) : PrivateReady p slots yb xb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

end VG.Proof.Ffdh.Arm

end

end

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
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
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
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
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
        (by have := p.maxLength; omega_using [scalarLength, this]) count length odd).mono
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

end

end

/-! Imported private-key checking satisfies the shared timing policy, including its status leakage. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateEntryCT.lean`, which only this module imported.
section

/-! The imported-private-key entry has fixed stack access addresses. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem privateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 24).seq (RelCT.block_append ((storeLocal_ct .r1 28).seq (RelCT.block_append ((storeLocal_ct .r2 32).seq (RelCT.block_append ((storeLocal_ct .r3 36).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r0 140 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateBodyCT.lean`, which only this module imported.
section

/-! Imported private-key checking reveals only public inputs and its documented scalar validity class. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem privateBody_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => PrivateMainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : PrivateMainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, h.value.after_frame frame rest (sourceSep h.valueStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack),
      by rw [rest.sp]; exact h.valueStack, by rw [rest.sp]; exact h.scalarStack,
      ⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact privateMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp) (by simp)
        peerLength positive scalarLength count length classification facts.2.1 facts.1 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateFnCT.lean`, which only this module imported.
section

/-! The imported-private-key callable reveals only public inputs and its scalar validity class. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem privateFn_ct {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => PrivateFnInput p yb xb1 s ∧ PrivateFnInput p yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, PrivateFnInput p yb xb s ∧ a = entered s
  have entry := privateEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) a
        (PrivateMainInput p [0, 44, 40, 36, 32, 28, 24] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (privateEntry_ok (entered s) input.args input.incoming input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.value.after_frame frame rest (sourceSep input.valueStack),
      input.scalar.after_frame frame rest (sourceSep input.scalarStack),
      by rw [rest.sp]; exact input.valueStack, by rw [rest.sp]; exact input.scalarStack,
      ⟩
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (privateBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      related.1.length related.1.positive related.1.scalarLength related.1.scalarCount length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem private_contract_ct : ConstantTime isa (Spec.Ffdh.checkPrivateContract abi 128).pre
    (Spec.Ffdh.checkPrivateContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := private_data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.checkPrivateContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6, p7, p8⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p0, ← p1, ← p2, ← p3, ← p5, ← p6] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, statusEq⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := private_input t ht (p := p) (yb := yb) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans domain) (p3.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p2]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    have status := (List.cons.inj statusEq).1
    rw [← domEq, ← peerEq] at status
    simp only [State.addr] at domainBytes peerBytes scalarBytes
    simp only [count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes] at status
    have classification := privateScalarClass_same p (Spec.Rsa.os2ip yb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip xb2) status
    exact (privateFn_ct (by rw [xLength, x2Length]) classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm

end

end


/-! Native ARMv7 imported private-key validation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def privateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x21 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x30 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x3000, 8448⟩]

theorem private_sat : ∃ s, (Spec.Ffdh.checkPrivateContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [privateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using privateSat

theorem private_verified : Verified target VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
    (Spec.Ffdh.checkPrivateContract abi 128) :=
  ⟨private_correct, private_contract_ct, private_sat⟩

end VG.Proof.Ffdh.Arm
