module

public import VerifiedGarbage.Proof.Rsa.X86.CvPair
import VerifiedGarbage.Proof.Rsa.X86.CvFailure
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Clearing all CRT outputs has a trace determined by their public lengths -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValues

theorem clear_trace (g : CallGeometry) (i : Fin 3) :
    RelCT isa (Pair g) (clear (2 * i.val)) (fun _ _ => True) := by
  have zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have head := VG.RelCT.block_append (VG.RelCT.seq
    (loadArguments_relCT (2 * i.val) (2 * i.val + 1) (g.args (2 * i.val)) (g.args (2 * i.val + 1))) zero)
  have loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq head loop).mono
  · intro s t h
    exact ⟨h.agree, (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc,
      (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc⟩
  · exact fun _ _ h => h

theorem clear_relCT (g : CallGeometry) (i : Fin 3) : RelCT isa (Pair g) (clear (2 * i.val)) (Pair g) := by
  intro s t tr ur sf tf h es et
  have eq := (clear_trace g i _ _ _ _ _ _ h es et).1
  obtain ⟨hs, _, _, _, ks⟩ := wp_result (clear_input_ok h.left i) es
  obtain ⟨ht, _, _, _, kt⟩ := wp_result (clear_input_ok h.right i) et
  exact ⟨eq, h.after hs ht ks kt (by decide)⟩

theorem failure_relCT (g : CallGeometry) :
    RelCT isa (Pair g) VG.Impl.Rsa.X86.CrtValues.failure (fun _ _ => True) :=
  (VG.RelCT.seq (clear_relCT g 0) (VG.RelCT.seq (clear_relCT g 1) (clear_relCT g 2))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86.CrtValues
