module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Finish
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! The native return path uses public control/output/stack addresses;
its consumed-byte count and saved register values do not affect timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Bignum.Arm

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original result, KeyDone p original result s

private theorem done_pins : Pins KeyCTDone [.r4] := by
  intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14]) s (fun t => t.gpr .r1 = p.up) := by
  obtain ⟨_, _, finished⟩ := h
  have controller := finished.controller
  have pointer := finished.usedPtr
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [controller.addr (by decide : 15 < 16), controller.addr (by decide : 11 < 16),
    controller.addr (by decide : 14 < 16), controller.read (by decide : 15 < 16),
    controller.read (by decide : 11 < 16), controller.read (by decide : 14 < 16), pointer]

theorem finish_ct : RelCT isa (Two KeyCTDone) (.block VG.Impl.Ffdh.Arm.KeySearch.finish) (fun _ _ => True) := by
  have stores : RelCT isa (Two fun (p : KeyPublic) s => s.gpr .r1 = p.up)
      (.block [.mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (two_taint [.r1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide))
    exact fun _ _ ⟨_, _, _, sp⟩ => sp
  change RelCT isa _ (.block (([VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11, VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14] ++
      [.mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) ++
        [.ldrSp .r9 4, .ldrSp .r10 8, .ldrSp .r11 12, .ldrSp .lr 20])) _
  refine RelCT.block_append (RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.r4] done_pins (by taint_decide) finish_pointer) stores)) ?_)
  exact (stackLoads_ct [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.KeySearch
