module
public import VerifiedGarbage.Proof.Dsa.X86.StreamStep

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Initializing the streaming accumulator and byte padding -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem zeroSlot_ok {n size m j : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hj : 0 < j) (hj9 : j < 9) :
    WP isa (zerosW (slot n j) (2 * n)) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n j) n = 0 ∧
      Outside base (slot n j) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  have b := slot_bound (n := n) hj9
  have sep := slot_le (n := n) (i := 0) (j := j) hj
  have hd := slot_header n j
  have sz := h.size_le
  have n0 : 0 < n := h.modulus.n0
  refine WP.mono (zerosW_ok h.scr (by omega) (by unfold stride at b; omega)) fun t ⟨O, V, K⟩ => ?_
  have len : 4 * (2 * n) = 8 * n := by omega
  rw [len] at O
  exact ⟨h.outside_keep K (by decide) (by decide) O (.inl (by unfold stride at sep; omega)) (by omega),
    by rw [wordsVal_eq_val32, V], O, K⟩

/-- Clearing slots six and seven before `rest`. -/
theorem streamInit_ok {n size m : Nat} {base : Addr} {s : State} {rest : Prog isa} {Q : State → Prop}
    (h : Context n m base size s)
    (k : ∀ t, Context n m base size t → wordsVal t.mem base (slot n 6) n = 0 →
      wordsVal t.mem base (slot n 7) n = 0 → Outs base (streamRanges n) s.mem t.mem →
      Keeps [.eax, .ebp, .edx] s t → WP isa rest t Q) :
    WP isa (.seq (zerosW (slot n 6) (2 * n)) (.seq (zerosW (slot n 7) (2 * n)) rest)) s Q := by
  refine WP.seq (WP.mono (zeroSlot_ok h (j := 6) (by decide) (by decide)) fun u ⟨cu, Yu, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroSlot_ok cu (j := 7) (by decide) (by decide)) fun v ⟨cv, Bv, Ov, Kv⟩ => ?_)
  have sep := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have bd := slot_bound (n := n) (i := 6) (by decide)
  have sz := h.size_le
  have nw := h.scr.nowrap
  have Yv : wordsVal v.mem base (slot n 6) n = 0 := by
    rw [wordsVal_eq_val32, Ov.val32 (by unfold stride at sep; omega)
      (by unfold stride at bd; omega), ← wordsVal_eq_val32, Yu]
  exact k v cv Yv Bv ((Outs.of_outside Ou (by simp [streamRanges])).trans (Outs.of_outside Ov (by simp [streamRanges])))
    (Ku.trans Kv)

end VG.Proof.Dsa.X86
