module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
import VerifiedGarbage.Proof.Framework.Omega

/-! # IA-32 DSA exponentiation with its callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem core_ranges_scratch {n e : Nat} (he : e ≤ 2 * n) :
    ∀ r ∈ setupRanges n ++ exponentRanges n e,
      ∃ w ∈ scratch n, w.1 ≤ r.1 ∧ r.1 + r.2 ≤ w.1 + w.2 := by
  intro r hr
  simp only [setupRanges, exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl | rfl | rfl) | rfl | rfl)
  all_goals
    first
    | exact ⟨(0, 64), List.mem_cons_self .., by decide, by decide⟩
    | refine ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩ <;>
        simp only [contextBytes, slot, stride] <;> omega

theorem core_saved {s t : State} {base : Addr} {n e : Nat} {g : Reg → BitVec 32}
    (O : Outs base (setupRanges n ++ exponentRanges n e) s.mem t.mem)
    (H : Saved s.mem (off base) g slots) : Saved t.mem (off base) g slots := by
  intro p hp
  have hp' : 8 ≤ p.2 ∧ p.2 + 4 ≤ 24 := by
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [show t.mem.readW (off base p.2) 32 = s.mem.readW (off base p.2) 32 from
    Mem.readW_congr (fun i hi => O _ (by
      intro r hr
      rw [ofs_off base (by omega)]
      simp only [setupRanges, exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl | rfl | rfl) | rfl | rfl) <;>
        simp only [slot, stride] <;> omega))]
  exact H p hp

theorem body_ok {s : State} {base : Addr} {size n e m : Nat}
    (E : Entry s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have nw := E.nowrap
  have hz24 : 24 ≤ size := by simp only [contextBytes, slot, stride] at hz; omega
  unfold body
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Saved, Ou, Ku⟩ => ?_)
  have vals : ∀ {d k : Nat}, 24 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 u.mem base d k = val32 s.mem base d k :=
    fun hd hk => Ou.val32 (by omega) hk
  have V : wordsVal u.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, vals (by simp only [slot]; omega) (by simp only [slot, stride]; omega),
      ← wordsVal_eq_val32, hv]
  refine WP.seq (WP.mono (core_ok Su hz hn hn48 he hen V hm1 hodd)
    fun v ⟨Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (restore_ok (Su.of_keeps Kv (by decide)) hz24 (core_saved Ov Saved))
    fun t R => ⟨?_, ?_, R.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R.mem, Vv, wordsVal_eq_val32, vals (by simp only [slot]; omega)
      (by simp only [slot, stride]; omega), vals (by simp only [slot]; omega)
      (by simp only [slot, stride]; omega), ← wordsVal_eq_val32]
  · rw [R.mem]
    refine (Outs.of_outside (Ou.mono (by decide) (by decide)) (List.mem_cons_self ..)).trans ?_
    intro x hx
    apply Ov x
    intro r hr
    obtain ⟨w, hw, lo, hi⟩ := core_ranges_scratch hen r hr
    have := hx w hw
    omega
  · exact (Kv.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R.rd, Kv.2.1, Ku.2.1]
  · rw [R.wr, Kv.2.2, Ku.2.2]

end VG.Proof.Dsa.X86.Pow
