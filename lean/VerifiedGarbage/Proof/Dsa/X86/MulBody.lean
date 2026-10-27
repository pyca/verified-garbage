module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.X86.Arith
import VerifiedGarbage.Proof.Dsa.X86.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Omega

/-! # IA-32 DSA products with their callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (Entry save_ok restore_ok)

/-- A word outside every range that changed keeps its value. -/
theorem Outs.readW32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hn : base.toNat + d + 4 ≤ 2 ^ 32) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega

theorem body_ok {s : State} {base : Addr} {size n m : Nat}
    (E : Entry s base size) (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulBody n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      Outs base (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have nw := E.nowrap
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  have hz24 : 24 ≤ size := by omega
  unfold mulBody
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Sv, Ou, Ku⟩ => ?_)
  have kept (i : Nat) (hi : i < 9) : wordsVal u.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    have := slot_bound (n := n) hi
    simp only [stride] at this
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact Ou.val32 (by simp only [slot]; omega) (by omega)
  refine WP.seq (WP.mono (contextSetup_ok Su hn (by omega) hz ((kept 0 (by decide)).trans hv) hm1 hodd)
    fun v ⟨Cv, _, R2, Ov, Kv⟩ => ?_)
  have setupVal (i : Nat) (hi : i = 5 ∨ i = 8) :
      wordsVal v.mem base (slot n i) n = wordsVal u.mem base (slot n i) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    rcases hi with rfl | rfl <;>
    · refine Ov.val32 (fun r hr => ?_) (by simp only [slot, stride]; omega)
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
  refine WP.seq (WP.mono (ordinaryMul_ok Cv R2) fun w ⟨Cw, Vw, Ow, Kw⟩ => ?_)
  have savedW : Saved w.mem (off base) s.gpr slots := by
    intro p hp
    have hp' : 8 ≤ p.2 ∧ p.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    rw [Outs.readW32 Ow (fun r hr => by
        simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega) (by omega),
      Outs.readW32 Ov (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega) (by omega)]
    exact Sv p hp
  have Kuw : Keeps powerClob u w := Kv.trans (Kw.mono (by decide))
  refine WP.mono (restore_ok (Su.of_keeps Kuw (by decide)) hz24 savedW)
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vw, setupVal 5 (.inl rfl), setupVal 8 (.inr rfl),
      kept 5 (by decide), kept 8 (by decide)]
  · rw [R'.mem]
    have cover : ∀ y : Nat, (∀ r ∈ scratch n, y < r.1 ∨ r.1 + r.2 ≤ y) →
        y < 8 ∨ 24 ≤ y ∧ ∀ r ∈ setupRanges n ++ productRanges n, y < r.1 ∨ r.1 + r.2 ≤ y := by
      intro y hy
      have h0 := hy (0, 64) (List.mem_cons_self ..)
      have h1 := hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      dsimp only at h0 h1
      simp only [contextBytes, slot, stride] at h1
      by_cases y8 : y < 8
      · exact .inl y8
      refine .inr ⟨by omega, fun r hr => ?_⟩
      simp only [setupRanges, productRanges, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [slot, stride] <;> omega
    intro x hx
    rcases cover _ hx with lo | ⟨hi, rest⟩
    · rw [Ow x (fun r hr => by
          simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega),
        Ov x (fun r hr => by
          simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
          have h0 := hx (0, 64) (List.mem_cons_self ..)
          dsimp only at h0
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega)]
      exact Ou x (.inl lo)
    · rw [Ow x (fun r hr => rest r (List.mem_append_right _ hr)),
        Ov x (fun r hr => rest r (List.mem_append_left _ hr))]
      exact Ou x (.inr (by omega))
  · exact (Kuw.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R'.rd, Kuw.2.1, Ku.2.1]
  · rw [R'.wr, Kuw.2.2, Ku.2.2]

end VG.Proof.Dsa.X86.Mul
