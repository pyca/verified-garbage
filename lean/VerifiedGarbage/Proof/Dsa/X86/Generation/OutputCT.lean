module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputArguments
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputArguments

/-! # Output copying and clearing depend only on public frame pointers and lengths -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def CopyArgsAt (p : PublicFrame) (s : State) : Prop :=
  s.gpr .esi = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.packed ∧
  s.gpr .edx = p.words 6 ∧ s.gpr .ecx = p.words 7

theorem outputCopy_ct : RelCT isa (Two (FrameAt [5, 6, 7])) outputCopy (fun _ _ => True) := by
  unfold outputCopy
  refine RelCT.seq (two_piece (Ψ := CopyArgsAt) [.esp] (frameAt_pins _) (by taint_decide) ?_) ?_
  · intro p s R
    refine WP.mono (outputArgs_ok R.1 (observedWords_rep p.base s)) fun _ ⟨si, dx, cx, _, _, _⟩ => ?_
    exact ⟨si.trans (congrArg (· + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.packed) (R.2 5 (by simp))),
      dx.trans (R.2 6 (by simp)), cx.trans (R.2 7 (by simp))⟩
  · refine two_taint [.esi, .edx, .ecx] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hs.1.trans ht.1.symm, hs.2.1.trans ht.2.1.symm, hs.2.2.trans ht.2.2.symm]

def ZeroArgsAt (p : PublicFrame) (s : State) : Prop := s.gpr .esi = p.words 6 ∧ s.gpr .ecx = p.words 7

theorem outputZeroHead_ok {p : PublicFrame} {s : State} (R : FrameAt [6, 7] p s) :
    WP isa (.block [.mov .esi (.mem (frameSlot 6)), .mov .ecx (.mem (frameSlot 7)), .mov .eax (.imm 0)]) s
      (ZeroArgsAt p) := by
  refine wp_movS (by rw [R.1.readSlot (by decide : 6 < 37), R.2 6 (by simp)]) fun a sa _ => ?_
  have Ra := R.keep sa.mem sa.keeps (by decide)
  refine wp_movS (by rw [Ra.1.readSlot (by decide : 7 < 37), Ra.2 7 (by simp)]) fun b ab _ =>
    wp_movS rfl fun t bt _ => WP.block_nil ?_
  exact ⟨(bt.other _ (by decide)).trans ((ab.other _ (by decide)).trans sa.gpr),
    (bt.other _ (by decide)).trans ab.gpr⟩

theorem outputZero_ct : RelCT isa (Two (FrameAt [6, 7])) outputZero (fun _ _ => True) := by
  unfold outputZero
  refine RelCT.seq (two_piece (Ψ := ZeroArgsAt) [.esp] (frameAt_pins _) (by taint_decide)
    (fun _ _ R => outputZeroHead_ok R)) ?_
  refine two_taint [.esi, .ecx] ?_ (by taint_decide)
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [hs.1.trans ht.1.symm, hs.2.trans ht.2.symm]

theorem finishOutput_ct : RelCT isa (Two (FrameAt [5, 6, 7, 19])) finishOutput (fun _ _ => True) := by
  unfold finishOutput
  refine RelCT.seq (two_piece (Ψ := fun p s => FrameAt [5, 6, 7, 19] p s ∧
    s.zf = some (decide (p.words 19 = 1))) [.esp] (frameAt_pins _) (by taint_decide) ?_) ?_
  · intro p s R
    refine WP.mono (frameSuccess_ok R.1 (observedWords_rep p.base s)) fun _ ⟨zf, mem, K⟩ => ?_
    exact ⟨R.keep mem K (by decide), by rw [zf]; unfold observedWords; rw [R.2 19 (by simp)]⟩
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · exact outputCopy_ct.mono (fun _ _ => two_mono (fun _ _ h => ⟨h.1.1.1, fun i hi => h.1.1.2 i (by simp_all; omega)⟩)) (fun _ _ h => h)
    · exact outputZero_ct.mono (fun _ _ => two_mono (fun _ _ h => ⟨h.1.1.1, fun i hi => h.1.1.2 i (by simp_all; omega)⟩)) (fun _ _ h => h)
end VG.Proof.Dsa.X86.Generation
