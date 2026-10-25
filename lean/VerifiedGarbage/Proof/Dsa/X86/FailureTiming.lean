module

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Constant-time clearing on public shape rejection -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def failureTaint : VG.X86.Taint.T := { workspaceTaint true with regs := .ofList [.edi, .esi, .ecx, .eax] }

theorem failureHead_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block [.mov .esi (.mem (sc (Layout.field .out))), .mov .ecx (.mem (sc (Layout.field .qLen))),
      .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)]) s fun t =>
      t.gpr .esi = pointerValue base s (.input .out) ∧
      t.gpr .ecx = pointerValue base s (.input .qLen) + pointerValue base s (.input .qLen) ∧
      t.gpr .eax = 0 ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  refine wp_movS (readSrc_sc hs (d := Layout.field .out) (by change 8228 ≤ size; omega)) fun s1 U1 _ => ?_
  refine wp_movS (readSrc_sc (hs.of_keeps U1.keeps (by decide))
    (d := Layout.field .qLen) (by change 8236 ≤ size; omega)) fun s2 U2 _ => ?_
  refine wp_addS rfl fun s3 U3 _ => ?_
  refine wp_movS rfl fun s4 U4 _ => WP.block_nil ⟨?_, ?_, U4.gpr, ?_⟩
  · rw [U4.other _ (by decide), U3.other _ (by decide), U2.other _ (by decide), U1.gpr]
    rfl
  · rw [U4.other _ (by decide), U3.gpr, U2.gpr, U1.mem]
    rfl
  · exact (((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans
      (U3.keeps.mono (by decide))).trans (U4.keeps.mono (by decide))

theorem failureHead_relCT (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out) ∧
      pointerValue base s (.input .qLen) = pointerValue base t (.input .qLen))
      (.block [.mov .esi (.mem (sc (Layout.field .out))), .mov .ecx (.mem (sc (Layout.field .qLen))),
        .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)]) (VG.X86.Taint.Agree failureTaint) := by
  intro s t tr ur sf tf ⟨S, T, P, Q⟩ E F
  have G : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have A : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi])
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact G
  have Check : VG.Taint.check taint (workspaceTaint false)
      (.block [.mov .esi (.mem (sc (Layout.field .out))), .mov .ecx (.mem (sc (Layout.field .qLen))),
        .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)]) (.block []) = some (zeroTaint false) := rfl
  obtain ⟨P1, Q1, A1, K1⟩ := wp_result (failureHead_ok S hz) E
  obtain ⟨P2, Q2, A2, K2⟩ := wp_result (failureHead_ok T hz) F
  refine ⟨(VG.Taint.check_sound Check A E F).1, ?_⟩
  apply agree_regs (rs := [.edi, .esi, .ecx, .eax])
  intro reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [K1.1 _ (by decide), K2.1 _ (by decide)]; exact G
  · exact P1.trans (P.trans P2.symm)
  · rw [Q1, Q2, Q]
  · exact A1.trans A2.symm

theorem signFailure_relCT (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out) ∧
      pointerValue base s (.input .qLen) = pointerValue base t (.input .qLen))
      (Entry.failure true) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Entry.failure Core.sequence
  dsimp only [ite_true, List.foldr]
  refine RelCT.seq (failureHead_relCT base size hz) (RelCT.seq ?_ (RelCT.block_nil (fun _ _ h => h)))
  exact checkedProgramChange (τ' := { failureTaint with flags := true })
    (hint := .loop failureTaint (.block [])) (by kernel_rfl) (by kernel_rfl)

theorem verifyFailure_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Entry.failure false)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := zeroTaint false) rfl rfl

end VG.Proof.Dsa.X86
