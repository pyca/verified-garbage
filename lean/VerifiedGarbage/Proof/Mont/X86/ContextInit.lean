module
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # Constructing the runtime Montgomery context -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

theorem modulus_low {n m : Nat} {base : Addr} {mem : Mem} (hn : 0 < n)
    (hv : wordsVal mem base (slot n 0) n = m) : m % 2 ^ 32 = w32 mem base (slot n 0) := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  rw [wordsVal_eq_val32, hk, val32] at hv
  have hl : w32 mem base (slot n 0) < 2 ^ 32 := (mem.readW (off base (slot n 0)) 32).isLt
  omega

def setupRanges (n : Nat) : List (Nat × Nat) :=
  [(0, 4), (slot n 3, 8 * n), (slot n 4, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem contextSetup_ok {n size m : Nat} {base : Addr} {s : State}
    (hs : Scr s base size) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : contextBytes n ≤ size) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (contextSetup n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have hd0 := slot_header n 0
  have hd1 := slot_header n 1
  have hd2 := slot_header n 2
  have hd3 := slot_header n 3
  have hd4 := slot_header n 4
  have s01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have s03 := slot_le (n := n) (i := 0) (j := 3) (by decide)
  have s04 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  have s13 := slot_le (n := n) (i := 1) (j := 3) (by decide)
  have s23 := slot_le (n := n) (i := 2) (j := 3) (by decide)
  have s34 := slot_le (n := n) (i := 3) (j := 4) (by decide)
  have low := modulus_low hn hv
  have lowodd : w32 s.mem base (slot n 0) % 2 = 1 := by omega
  unfold contextSetup
  refine WP.seq (WP.mono (setupInverse_ok hs
    (by unfold stride at b0; omega) (by unfold stride at b0; omega) lowodd) fun u ⟨inv, O, K⟩ => ?_)
  have cu : Context n m base size u := by
    refine ⟨hs.of_keeps K (by decide), hz, ⟨hn, ?_, ?_, ?_, ?_⟩, hm1, ?_⟩
    · change slot n 0 + 8 * n ≤ size; unfold stride at b0; omega
    · change slot n 1 + 8 * n ≤ size; unfold stride at b1; omega
    · change slot n 0 + 8 * n ≤ slot n 1 ∨ slot n 1 + 8 * n ≤ slot n 0
      unfold stride at s01; omega
    · change wordsVal u.mem base (slot n 0) n = m
      rw [wordsVal_eq_val32, O.val32 (by omega) (by unfold stride at b0; omega), ← wordsVal_eq_val32, hv]
    · rw [Nat.add_mod, Nat.mul_mod, low] at ⊢
      rw [Nat.add_mod, Nat.mul_mod] at inv
      simpa only [Nat.mod_eq_of_lt (s.mem.readW (off base (slot n 0)) 32).isLt] using inv
  refine WP.seq (WP.mono (one_ok cu.scr hn (by unfold stride at b3; omega)) fun v ⟨Ov, Vv, Kv⟩ => ?_)
  have cv := cu.outside_keep Kv (by decide) (by decide) Ov
    (.inl (by unfold stride at s03; omega)) (by omega)
  refine WP.mono (powerTwo_ok cv.scr cv.modulus
    (context_opLay hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by change slot n 4 + 8 * n ≤ slot n 0 ∨ slot n 0 + 8 * n ≤ slot n 4; unfold stride at s04; omega)
    hm1 (by change 0 < 128 * n; omega) hn32) fun t ⟨Vt, _, Mt, Ot, Kt⟩ => ?_
  have inverseT : (m * w32 t.mem base 0 + 1) % 2 ^ 32 = 0 := by
    have vv : val32 t.mem base 0 1 = val32 v.mem base 0 1 := by
      apply Ot.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [contextMod] <;> omega
      · decide
    have vv' : w32 t.mem base 0 = w32 v.mem base 0 := by
      simpa only [val32, Nat.mul_zero, Nat.add_zero] using vv
    rw [vv']; exact cv.inverse
  refine ⟨⟨cv.scr.of_keeps Kt (by decide), hz, Mt, hm1, inverseT⟩, ?_, Vt, ?_,
    (((K.mono (by decide)).trans (Kv.mono (by decide))).trans Kt)⟩
  · rw [wordsVal_eq_val32]
    have keep : val32 t.mem base (slot n 3) (2 * n) = val32 v.mem base (slot n 3) (2 * n) := by
      apply Ot.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [contextMod, accLen, words] <;>
          unfold stride at s13 s23 s34 <;> omega
      · unfold stride at b3; omega
    rw [keep, ← wordsVal_eq_val32, Vv]
  · have oo : Outs base (setupRanges n) s.mem u.mem := Outs.of_outside O (by simp [setupRanges])
    have ov : Outs base (setupRanges n) u.mem v.mem := Outs.of_outside Ov (by simp [setupRanges])
    exact (oo.trans ov).trans (Ot.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [setupRanges, contextMod, accLen, words] <;> omega))

end VG.Proof.Mont.X86.Dynamic
