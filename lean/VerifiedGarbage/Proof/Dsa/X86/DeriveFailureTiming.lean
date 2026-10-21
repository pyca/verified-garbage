module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming

/-! # Invalid-domain clearing has a fixed public byte count -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveFailureHead_ok {s : State} {base : Addr} {size len : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block [.mov .esi (.mem (sc (Layout.field .out))),
      .mov .ecx (.imm (BitVec.ofNat 32 len)), .mov .eax (.imm 0)]) s fun t =>
      t.gpr .esi = pointerValue base s (.input .out) ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧
      t.gpr .eax = 0 ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  refine wp_movS (readSrc_sc hs (by change 8228 ≤ size; omega)) fun s1 U1 _ => ?_
  refine wp_movS rfl fun s2 U2 _ => ?_
  refine wp_movS rfl fun s3 U3 _ => WP.block_nil ⟨?_, ?_, U3.gpr, ?_⟩
  · rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr]; rfl
  · rw [U3.other _ (by decide), U2.gpr]
  · exact ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))

theorem deriveFailure_relCT (pLen qLen : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out))
      (Generate.deriveFailure pLen qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.deriveFailure Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (R := VG.X86.Taint.Agree failureTaint) ?_
    (RelCT.seq (checkedProgramChange (τ' := { failureTaint with flags := true })
      (hint := .loop failureTaint (.block [])) rfl rfl) (RelCT.block_nil (fun _ _ h => h)))
  intro s t tr ur sf tf ⟨S, T, P⟩ E F
  have G : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have Agree : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi]); intro reg member
    obtain rfl := List.mem_singleton.mp member; exact G
  have Head : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.mov .esi (.mem (sc (Layout.field .out))),
        .mov .ecx (.imm (BitVec.ofNat 32 (3 * pLen + 2 * qLen))), .mov .eax (.imm 0)])
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
    erased_relCT _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0), .mov .eax (.imm 0)])
      (.block []) rfl rfl rfl rfl
  obtain ⟨Ps, Cs, As, Ks⟩ := wp_result (deriveFailureHead_ok S hz) E
  obtain ⟨Pt, Ct, At, Kt⟩ := wp_result (deriveFailureHead_ok T hz) F
  refine ⟨(Head _ _ _ _ _ _ Agree E F).1, ?_⟩
  apply agree_regs (rs := [.edi, .esi, .ecx, .eax])
  intro reg member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact G
  · exact Ps.trans (P.trans Pt.symm)
  · exact Cs.trans Ct.symm
  · exact As.trans At.symm

end VG.Proof.Dsa.X86
