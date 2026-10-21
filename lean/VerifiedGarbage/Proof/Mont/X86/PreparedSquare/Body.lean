module

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.FrameArgs

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Layout

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry

public import VerifiedGarbage.Proof.Framework.Semantics

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Cache
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryCore
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.FrameRestore
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.MemoryContract
public import VerifiedGarbage.Proof.Mont.X86.Compact.Correct
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared

/-! # A callable prepared square restores the ABI and meets multiplication's contract -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Spec.Rsa.Mont hiding Keeps

theorem body_ok {s : State} (A : Compact.Entry s) (same : arg s 3 = arg s 4) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.body s fun u => abiPreserved s u ∧ Compact.Result s u.mem := by
  let W := Compact.wsOf s
  let w := wOf s.mem W
  let S := arrAt w 2
  let o := arrAt w (arg s 2).toNat
  have fit : arrAt w 8 ≤ Compact.lenOf s := by
    simpa only [Compact.lenOf, Nat.mul_comm] using A.layout.2.2.1
  have lay := layout_bounds fit A.left
  have outFit := VG.Proof.Mont.X86.Compact.array_fit fit A.output.1
  have apart := VG.Proof.Mont.X86.Compact.operand_apart (w := w) A.output
  have scratchSpan : S + 8 * (2 * w) + 32 = arrAt w 4 := by unfold S arrAt hdrBytes; omega
  have header : 128 ≤ S := by unfold S arrAt hdrBytes; omega
  have modulus : arrAt w 0 = 256 := by simp [arrAt, hdrBytes]
  have outHeader : 128 ≤ o := by unfold o arrAt hdrBytes; omega
  have metadata := Compact.layout_metadata (A := arg s) A.layout A.left.1 A.right.1
  change Compact.Metadata s.mem W (arg s) (2 * w) S (arrAt w 0)
    (arrAt w (arg s 3).toNat) (arrAt w (arg s 4).toNat) at metadata
  rw [modulus] at metadata
  unfold VG.Impl.Mont.X86.PreparedSquare.body
  refine WP.seq (WP.mono (cache_ok (raw_ws A) (raw_args A) A.ws_toNat.symm metadata header
    (by have := lay.scr; omega)) ?_)
  rintro t ⟨eax, ebx, esi, ebp, edi, saved, O, K⟩
  have K7 : Keeps clob7 s t := K
  have Oall : Outs W [(0, Compact.lenOf s)] s.mem t.mem :=
    Outs.of_outside (O.mono (o' := 0) (n' := Compact.lenOf s) (by omega) (by have := lay.scr; omega)) (by simp)
  have args := original_args A K7 (by decide) ((raw_args A).of_keeps K7 (by decide) Oall)
  have hw := entered_ws ((raw_ws A).of_keeps K7)
  have scratch : w32 (entered t).mem W 80 = (W.toNat + S) % 2 ^ 32 := by
    rw [entered_w32 A K7 (by decide) (by have := A.headerFit; omega), O.w32 (by omega) (by omega)]
    exact metadata.scratch
  have savedent := entered_saved A K7 (by decide) (by have := lay.scr; omega) saved
  have core : WP isa VG.Impl.Mont.X86.PreparedSquare.core (entered t) fun u =>
      Outs W [(S + 16, 8 * (2 * w) + 16), (o, 4 * (2 * w))] (entered t).mem u.mem ∧
      Compact.Result s u.mem ∧ Keeps clob7 (entered t) u := by
    refine WP.mono (entry_core A same K7 O eax ebx esi ebp edi) ?_
    rintro u ⟨F, low, congruence, Ku⟩
    refine ⟨F, ⟨?_, ?_, entry_keeps A K7 (by decide) O F⟩, Ku⟩
    · rw [Compact.numAt_val32, Compact.numAt_val32]
      change val32 u.mem W o (2 * w) < val32 s.mem W (arrAt w 0) (2 * w)
      rwa [modulus]
    · rw [Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32, ← same]
      change val32 u.mem W o (2 * w) * 2 ^ (64 * w) % val32 s.mem W (arrAt w 0) (2 * w) =
        val32 s.mem W (arrAt w (arg s 3).toNat) (2 * w) *
          val32 s.mem W (arrAt w (arg s 3).toNat) (2 * w) % val32 s.mem W (arrAt w 0) (2 * w)
      rw [modulus, show 64 * w = 32 * (2 * w) by omega]
      simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using congruence
  refine WP.mono (frame_restore (by rw [K7.1 .esp (by decide)]; exact A.stackFit) hw args A.ws_toNat.symm
    scratch header outHeader lay.scr (by omega) (by omega) savedent core) ?_
  rintro u ⟨ebx', esi', ebp', edi', sp, F, result⟩
  refine ⟨⟨?_, ?_⟩, result⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ebx'
    · exact esi'
    · exact edi'
    · exact ebp'
    · exact sp.trans (K7.1 .esp (by decide))
  · have Fall : Outs W [(0, Compact.lenOf s)] (entered t).mem u.mem := F.cover (by
      intro r hr
      refine ⟨(0, Compact.lenOf s), by simp, by omega, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_using [lay.scr, outFit])
    exact return_word A K7 (by decide) Oall Fall

end VG.Proof.Mont.X86.PreparedSquare
