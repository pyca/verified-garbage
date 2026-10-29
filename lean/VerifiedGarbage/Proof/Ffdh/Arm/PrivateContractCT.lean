module

public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.PrivateCorrect
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePre
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateFn
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
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
