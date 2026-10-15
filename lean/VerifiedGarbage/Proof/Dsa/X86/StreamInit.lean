module

public import VerifiedGarbage.Proof.Dsa.X86.StreamLoop

/-! # Initializing the streaming accumulator and byte padding -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem zeroSlot_ok {n size m j : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hj : 0 < j) (hj9 : j < 9) :
    WP isa (.block (zeros (slot n j) (2 * n))) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n j) n = 0 ∧
      Outside base (slot n j) (8 * n) s.mem t.mem ∧ Keeps [.eax] s t := by
  have b := slot_bound (n := n) hj9
  have sep := slot_le (n := n) (i := 0) (j := j) hj
  have hd := slot_header n j
  have sz := h.size_le
  refine WP.mono (zeros_ok h.scr (by unfold stride at b; omega)) fun t ⟨O, V, K⟩ => ?_
  have len : 4 * (2 * n) = 8 * n := by omega
  rw [len] at O
  exact ⟨h.outside_keep K (by decide) (by decide) O (.inl (by unfold stride at sep; omega)) (by omega),
    by rw [wordsVal_eq_val32, V], O, K⟩

theorem streamInit_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) :
    WP isa (.block (zeros (slot n 6) (2 * n) ++ zeros (slot n 7) (2 * n) ++
      ([.mov .esi (.imm 0)] : List Instr))) s fun t =>
      Context n m base size t ∧ t.gpr .esi = 0 ∧
      wordsVal t.mem base (slot n 6) n = 0 ∧ wordsVal t.mem base (slot n 7) n = 0 ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (zeroSlot_ok h (j := 6) (by decide) (by decide)) fun u ⟨cu, Yu, Ou, Ku⟩ => ?_)
  refine WP.block_append (WP.mono (zeroSlot_ok cu (j := 7) (by decide) (by decide)) fun v ⟨cv, Bv, Ov, Kv⟩ => ?_)
  refine wp_movS rfl fun t vt _ => WP.block_nil ?_
  have ct : Context n m base size t := ⟨cv.scr.of_keeps vt.keeps (by decide), cv.size_le,
    vt.mem ▸ cv.modulus, cv.gt_one, vt.mem ▸ cv.inverse⟩
  have sep := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have bd := slot_bound (n := n) (i := 6) (by decide)
  have sz := h.size_le
  have nw := h.scr.nowrap
  have Yv : wordsVal v.mem base (slot n 6) n = 0 := by
    rw [wordsVal_eq_val32, Ov.val32 (by unfold stride at sep; omega)
      (by unfold stride at bd; omega), ← wordsVal_eq_val32, Yu]
  refine ⟨ct, vt.gpr, vt.mem ▸ Yv, vt.mem ▸ Bv, ?_, ?_⟩
  · rw [vt.mem]
    exact (Outs.of_outside Ou (by simp [streamRanges])).trans (Outs.of_outside Ov (by simp [streamRanges]))
  · exact (((Ku.mono (by decide)).trans (Kv.mono (by decide))).widen vt.keeps)

end VG.Proof.Dsa.X86
