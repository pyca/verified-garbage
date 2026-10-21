module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadPrime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # Import frames preserve initialized constants and other persistent inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem loadPrime_preserves_num {m m' : Mem} {B : Addr} {n k out j : Nat}
    (width : k ≤ n) (positive : 1 ≤ j) (different : j ≠ out) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (loadPrimeRanges n k out) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [loadPrimeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have last := arr_end (w := n) (show 0 < j by omega)
    unfold S at last
    exact Or.inr (by omega)
  · have D := arr_disj (w := n) different
    simp only at D ⊢
    unfold S at D ⊢
    omega

theorem loadPrime_stage_frame {m m' : Mem} {B : Addr} {n k out : Nat} (width : k ≤ n)
    (O : Outs B (loadPrimeRanges n k out) m m') : Outs B (stageRanges n [out]) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [loadPrimeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact stage_cover_temp (by simp only [arr, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _) (by unfold arr S; omega)
  · exact stage_cover_array (by simp) (Nat.le_refl _)

theorem loadExponent_scratch_frame {s : VG.X86.State} {B : Addr} {Z n : Nat} {m m' : Mem}
    (h : Ws s B Z n 32) (O : Outs B (loadExponentRanges n) m m') : Frame [⟨B, Z⟩] m m' := by
  have head := h.hdr_le
  apply outs_scratch_frame (by have := h.workspace.nowrap; omega) O
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · unfold kEv hdr at *
    omega
  · exact h.arr_fit (by decide)

theorem Input.afterExponent {E : Environment} {s t : VG.X86.State} {regs : List VG.X86.Reg}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : VG.Proof.Mont.X86.Keeps regs s t)
    (O : Outs E.base (loadExponentRanges E.n) s.mem t.mem) : Input E t := by
  apply h.afterOuts ws K ?_ O
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · decide
  · exact Nat.le_trans (by decide : 72 ≤ hdr) (Nat.le_add_right ..)

end VG.Proof.RsaKeyGen.X86.Key
