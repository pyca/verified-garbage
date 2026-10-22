module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingInit
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace

/-! The public arithmetic arguments survive every conditional halving. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num)
open VG.Impl.Dsa.X86.Generation (arithmeticLay)

structure TimedHalving (base : Addr) (bytes len count value budget j : Nat) (sp : BitVec 32)
    (args : Nat → Byte) (initial s : State) : Prop where
  run : HalvingLoopInv arithmeticLay base bytes len count value budget j initial s
  arguments : ArithmeticFrame sp args s

theorem halving_init_public {s : State} {base : Addr} {bytes len count value : Nat} {sp : BitVec 32}
    {args : Nat → Byte} (ws : RtWs arithmeticLay s base bytes len count) (arrays : 2 ≤ count)
    (current : num s.mem base (kw len) 0 = value) (A : ArithmeticFrame sp args s) :
    WP isa (.block (Impl.Dsa.X86.Generation.halvingInit arithmeticLay)) s fun t =>
      TimedHalving base bytes len count value (32 * kw len) 0 sp args s t := by
  refine WP.mono (halving_init ws (by omega) current) ?_
  rintro t ⟨ht, F, K⟩
  exact ⟨⟨ht, F.mono (by simp) (by simp), K.mono (by decide)⟩,
    A.after_key ws K (by decide) F (by simp) (by decide)⟩

theorem halving_step_public {initial s : State} {base : Addr} {bytes len count value budget j : Nat}
    {sp : BitVec 32} {args : Nat → Byte}
    (h : TimedHalving base bytes len count value budget j sp args initial s)
    (arrays : 2 ≤ count) (hj : j < budget) (bound : budget ≤ 16384) :
    WP isa (Impl.Dsa.X86.Generation.halvingStep arithmeticLay) s fun t =>
      TimedHalving base bytes len count value budget (j + 1) sp args initial t ∧
      t.zf = some (decide (budget - (j + 1) = 0)) := by
  have tcBound : (halvingValues value j).2 ≤ 16384 :=
    Nat.le_trans (VG.Proof.Rsa.halve_count_le value j) (by omega)
  refine WP.mono (halving_step h.run.state arrays tcBound (by omega)) ?_
  rintro t ⟨ht, F, zf, K⟩
  have next : VG.Proof.Rsa.halveStep (halvingValues value j) = halvingValues value (j + 1) :=
    (Function.iterate_succ_apply' _ _ _).symm
  rw [next, show budget - j - 1 = budget - (j + 1) by omega] at ht
  rw [show budget - j - 1 = budget - (j + 1) by omega] at zf
  have A := h.arguments.after_key h.run.state.workspace K (by decide) F
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega) (by decide)
  exact ⟨⟨⟨ht, h.run.frame.trans F, h.run.keeps.trans K⟩, A⟩, zf⟩

end VG.Proof.Dsa.X86.Generation
