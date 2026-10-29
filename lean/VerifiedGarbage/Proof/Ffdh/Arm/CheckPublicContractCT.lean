module

public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicCorrect
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntry
/-! The native public check has the timing policy of the shared FFDH signature. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CheckPublicBodyCT.lean`, which only this module imported.
section

/-! The public-value body has a trace determined by its documented public inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicBody_ct {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (length : yb.length = p.k) :
    RelCT isa (fun s t => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main) (fun _ _ => True) := by
  let Q := fun s : State => PublicMainInput p (60 :: 56 :: slots) yb s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : PublicMainInput p slots yb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    refine ⟨⟨context, h.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.separate), ?_⟩, zero⟩
    rw [rest.sp]; exact h.separate
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckPublic.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (checkPublicMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp) length facts.2.1 facts.1).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head wp wp branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CheckPublicFnCT.lean`, which only this module imported.
section

/-! The complete callable public check reveals only public FFDH inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicFn_ct {p : Inputs} {yb : List Byte} (length : yb.length = p.k) :
    RelCT isa (fun s t => CheckPublicFnInput p yb s ∧ CheckPublicFnInput p yb t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPublic.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, CheckPublicFnInput p yb s ∧ a = entered s
  have entry := checkPublicEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) a
      (PublicMainInput p [0, 36, 32, 28, 24] yb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (checkPublicEntry_ok (entered s) input.args input.incoming
      input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    refine ⟨context, input.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact input.valueStack), ?_⟩
    rw [rest.sp]; exact input.valueStack
  have body := relCT_chain entry wp wp
    (checkPublicBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) length)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem checkPublic_contract_ct : ConstantTime isa (Spec.Ffdh.checkPublicContract abi 128).pre
    (Spec.Ffdh.checkPublicContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPublic.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, base, domain, value, count, capacity, domainBytes, valueBytes, inputS⟩ := checkPublic_data s hs
  have lengths (a : State) (h : (Spec.Ffdh.checkPublicContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_pub [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [lengths s hs, lengths t ht, ← p0, ← p1, ← p2, ← p3] at byteEq
  obtain ⟨domEq, yEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have inputT := checkPublic_input t ht (p := p) (yb := yb)
    (p5.symm.trans base) (p0.symm.trans domain) (p3.symm.trans value)
    (by rw [← p2]; exact count) (by rw [← p6]; exact capacity) ?_ ?_
  · exact (checkPublicFn_ct inputS.length s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← value, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← yEq, value, count]
    exact valueBytes

end VG.Proof.Ffdh.Arm
