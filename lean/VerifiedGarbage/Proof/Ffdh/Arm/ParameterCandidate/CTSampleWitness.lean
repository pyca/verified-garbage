module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTWitnessMask
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Sample import and truncation reuse RSA's operand import timing proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure WitnessSampleData where
  mask : WitnessMaskData
  source : BitVec 32

structure WitnessSampleStart (p : WitnessSampleData) (s : State) : Prop where
  mask : WitnessMaskStart p.mask s
  stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.mask.base, 8 * p.mask.capacity⟩
  bitsFit : p.mask.bits ≤ 64 * p.mask.words
  sourceFit : p.source.toNat + (p.mask.bits + 7) / 8 ≤ 2 ^ 32
  sourceRead : InRegions (s.rd ++ s.wr) (State.addr p.source) ((p.mask.bits + 7) / 8)
  sourceSep : (⟨State.addr p.source, (p.mask.bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr p.mask.base, 8 * p.mask.capacity⟩
  source : s.gpr .r4 = p.source
  count : s.gpr .r6 = BitVec.ofNat 32 ((p.mask.bits + 7) / 8)

private theorem sampleImport_ok (p : WitnessSampleData) (s : State) (h : WitnessSampleStart p s) :
    WP isa (VG.Impl.Bignum.Arm.importOperand 1) s (WitnessMaskStart p.mask) := by
  refine WP.mono (importOperand_ok s h.mask.ready (o := 1) (by decide) (by decide)
    (by have := h.mask.positive; omega) (by have := h.bitsFit; omega) h.sourceFit h.sourceRead h.sourceSep h.source h.count) ?_
  rintro t ⟨ready, _, _, frame, rest⟩
  have saved : t.mem.readW (State.addr (t.sp + 44#32)) 32 = BitVec.ofNat 32 p.mask.bits := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 44#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.mask.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.mask.stack.nowrap; omega)]
      exact h.stackSep.sub_left (Offset.sub_base _ (by decide : 44 + 4 ≤ 72))
  exact ⟨ready, by rw [rest.sp]; exact h.mask.stack.congr rest.wr, h.mask.positive, h.mask.bound, saved⟩

theorem sampleWitness_ct : RelCT isa (Two WitnessSampleStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness (fun _ _ => True) := by
  have importTrace : RelCT isa (Two WitnessSampleStart) (VG.Impl.Bignum.Arm.importOperand 1) (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact importOperand_ct (by decide : 1 < 8) _ _ _ _ _ _
      ⟨left.mask.ready, right.mask.ready, left.source, right.source, left.count, right.count, sp⟩ runS runT
  exact (two_post importTrace sampleImport_ok).seq
    (witnessMask_ct.mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.mask, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
