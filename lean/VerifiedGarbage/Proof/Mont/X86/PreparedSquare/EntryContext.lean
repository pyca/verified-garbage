module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.FrameArgs
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.TimingArgs
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingGeometry
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingEntry
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Cached entry state retains the existing public prepared timing context -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Spec.Rsa.Mont hiding Keeps

theorem entry_context {s t : State} (A : Compact.Entry s) (K : Keeps clob7 s t)
    (O : Outside (Compact.wsOf s) (arrAt (wOf s.mem (Compact.wsOf s)) 2) 16 s.mem t.mem) :
    Compact.Context (Compact.geometry s) (entered t) := by
  let W := Compact.wsOf s
  let w := wOf s.mem W
  let S := arrAt w 2
  change Outside W S 16 s.mem t.mem at O
  have fit : arrAt w 8 ≤ Compact.lenOf s := by
    simpa only [Compact.lenOf, Nat.mul_comm] using A.layout.2.2.1
  have header : 128 ≤ S := by unfold S arrAt hdrBytes; omega
  have sf : S + 16 ≤ Compact.lenOf s := by unfold S arrAt hdrBytes at *; omega
  have Oall : Outs W [(0, Compact.lenOf s)] s.mem t.mem :=
    Outs.of_outside (O.mono (o' := 0) (n' := Compact.lenOf s) (by omega) (by omega)) (by simp)
  have args := original_args A K (by decide) ((raw_args A).of_keeps K (by decide) Oall)
  have M := entered_metadata A K (by decide)
    ((Compact.layout_metadata (A := arg s) A.layout A.left.1 A.right.1).keep O header)
  refine ⟨entered_ws ((raw_ws A).of_keeps K), ?_, ?_, ?_, ?_⟩
  · constructor
    · intro i index
      change readSrc (entered t) (.mem (VG.Impl.Mont.X86.Compact.arg i)) = some (if i < 5 then arg s i else 0)
      rw [ite_eq_left index]
      exact args.read i index
    · exact args.far
  · exact ⟨M.width, M.aIndex, M.bIndex, M.scratch, M.modulus, M.left, M.right⟩
  · change w32 (entered t).mem W (64 + 8 * (arg s 2).toNat) =
      (W.toNat + arrAt w (arg s 2).toNat) % 2 ^ 32
    rw [entered_w32 A K (by decide) (by have := A.headerFit; have := A.output.1; omega),
      O.w32 (by have := A.output.1; omega) (by have := A.output.1; omega)]
    exact Compact.layout_pointer_low A.layout A.output.1
  · refine timing_wf_transport A.timing_wf ?_ ?_
    · rw [entered, Compact.entered, pushed_esp, pushed_esp, K.1 .esp (by decide)]
      rfl
    · rw [entered, Compact.entered, pushed_wr, pushed_wr, K.1 .esp (by decide), K.2.2]
      rfl

end VG.Proof.Mont.X86.PreparedSquare
