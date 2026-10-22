module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingStep
public import VerifiedGarbage.Proof.Rsa.RecoverHalving

/-! A fixed public number of conditional halvings implements the shared iteration. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep)
open VG.Impl.Rsa.X86.KeyRt (Lay)

abbrev halvingValues (value j : Nat) : Nat × Nat := VG.Proof.Rsa.halveStep^[j] (value, 0)

structure HalvingLoopInv (L : Lay) (base : Addr) (bytes len count value budget j : Nat)
    (initial s : State) : Prop where
  state : HalvingState L base bytes len count (halvingValues value j).1 (halvingValues value j).2 (budget - j) s
  frame : Keep base (kw len) [0, 1] [28, 20, 56] initial.mem s.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp] initial s

theorem halving_loop {L : Lay} {initial s : State} {base : Addr} {bytes len count value budget : Nat}
    (I : HalvingLoopInv L base bytes len count value budget 0 initial s)
    (arrays : 2 ≤ count) (positive : 0 < budget) (bound : budget ≤ 16384) :
    WP isa (.loop (Impl.Dsa.X86.Generation.halvingStep L) .ne) s fun t =>
      HalvingLoopInv L base bytes len count value budget budget initial t := by
  refine WP.loop (M := isa)
    (fun remaining t => ∃ j, remaining = budget - j ∧ j < budget ∧
      HalvingLoopInv L base bytes len count value budget j initial t)
    ?_ budget s ⟨0, rfl, positive, I⟩
  rintro remaining t ⟨j, rfl, hj, J⟩
  have tcBound : (halvingValues value j).2 ≤ 16384 :=
    Nat.le_trans (VG.Proof.Rsa.halve_count_le value j) (by omega)
  refine WP.mono (halving_step J.state arrays tcBound (by omega)) ?_
  rintro u ⟨hu, F, zf, K⟩
  have next : VG.Proof.Rsa.halveStep (halvingValues value j) = halvingValues value (j + 1) :=
    (Function.iterate_succ_apply' _ _ _).symm
  rw [next, show budget - j - 1 = budget - (j + 1) by omega] at hu
  rw [show budget - j - 1 = budget - (j + 1) by omega] at zf
  have J' : HalvingLoopInv L base bytes len count value budget (j + 1) initial u :=
    ⟨hu, J.frame.trans F, J.keeps.trans K⟩
  by_cases done : j + 1 = budget
  · exact .inl ⟨by simp only [eval, zf, done, Nat.sub_self, decide_true, Option.map_some, Bool.not_true], done ▸ J'⟩
  · have nonzero : budget - (j + 1) ≠ 0 := by omega
    exact .inr ⟨by simp only [eval, zf, decide_eq_false nonzero, Option.map_some, Bool.not_false],
      budget - (j + 1), by omega, j + 1, rfl, by omega, J'⟩

end VG.Proof.Dsa.X86.Generation
