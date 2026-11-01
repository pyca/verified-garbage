module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDerivePre
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveTailCT
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveFn
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! The derivation's timing depends on the domain, the lengths and the status alone. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveMainCT.lean`, which only this module imported.
section

/-! The derivation branches only on the scalar's validity, which its status discloses. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

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
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveEntryCT.lean`, which only this module imported.
section

/-! The public-value derivation's entry uses fixed local and incoming stack slots. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem deriveEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 4).seq (RelCT.block_append ((storeLocal_ct .r2 24).seq (RelCT.block_append ((storeLocal_ct .r3 28).seq (RelCT.block_append ((loadLocal_ct .r3 128 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 32).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r0 140 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveFnCT.lean`, which only this module imported.
section

/-! Invalid-domain handling, the entry and the frame reveal no scalar data: the complete
derivation is constant time for scalars of one length and validity. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head
        (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))
      (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => MainInput p (60 :: 56 :: slots) xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : MainInput p slots xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    exact ⟨⟨context, h.calls.after rest,
      h.scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact h.scalarStack),
      by rw [rest.sp]; exact h.scalarStack, h.output.after rest, h.workspaceSep,
      by rw [rest.sp]; exact h.stackSep⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact saved d hd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact main_ct backend stable' (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h40]) (by simp [h44]) (by simp) (by simp) saved'
        positive scalarLength count length classification facts.2.1 facts.1 facts.2.2 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

theorem fn_ct (backend : MontBackend) {p : Inputs} {xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => FnInput p xb1 s ∧ FnInput p xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p xb s ∧ a = entered s
  have entry := deriveEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) a (MainInput p [0, 44, 40, 32, 28, 24, 4] xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (deriveEntry_ok (entered s) input.args input.incoming input.out input.domain
      input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    exact ⟨context, input.calls.after rest,
      input.scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact input.scalarStack),
      by rw [rest.sp]; exact input.scalarStack, input.output.after rest, input.workspaceSep,
      by rw [rest.sp]; exact input.stackSep⟩
  unfold VG.Impl.Ffdh.Arm.SharedDerive.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by intro d hd; revert d; decide) related.1.positive related.1.scalarLength
      related.1.scalarCount length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm.SharedDerive
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa
    (Spec.Ffdh.derivePublicContract abi 176).pre (Spec.Ffdh.derivePublicContract abi 176).pub
    (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, xb, base, out, domain, scalar, publicValue, count, capacity, privateCount,
    domainBytes, scalarBytes, inputS⟩ := data s hs
  sig_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  rw [← p2, ← p3, ← p4, ← p5, ← p6] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have domT : Spec.Rsa.bytesAt t.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom := by
    rw [← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  have inputT := input t ht (p := p) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p5.symm.trans scalar) publicValue
    (by rw [← p4]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount)
    (by rw [← p3]; exact domT) rfl
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
  have status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb2) := by
    have eq := List.singleton_inj.mp statusEq
    simp only [State.addr] at domainBytes scalarBytes domT
    rw [count, scalar, privateCount, ← domEq, domain, domainBytes, scalarBytes] at eq
    exact eq
  have classification : (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p) := by
    have a := keyStatus_two_iff p (Spec.Rsa.os2ip xb)
    have b := keyStatus_two_iff p (Spec.Rsa.os2ip xb2)
    rw [status] at a
    have n := a.symm.trans b
    exact ⟨fun h => Classical.byContradiction fun h2 => n.mpr h2 h,
      fun h => Classical.byContradiction fun h1 => n.mp h1 h⟩
  exact (fn_ct backend (by rw [xLength, x2Length]) classification s t tr1 tr2 u v
    ⟨inputS, inputT, sp⟩ e1 e2).1

end VG.Proof.Ffdh.Arm.SharedDerive
