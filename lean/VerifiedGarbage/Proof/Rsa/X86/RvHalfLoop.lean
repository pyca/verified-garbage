module

public import VerifiedGarbage.Proof.Rsa.X86.RvHalfStep

/-! # The public number of halving iterations -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Recover

theorem halfLoop_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {m c : Nat}
    (h : HI g s0 A m c 0 s) (positive : 0 < c) (bound : c ≤ 16384) :
    WP isa (.loop (halfBody g.n) .ne) s (HI g s0 A m c c) := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = c ∧ 0 < j ∧ HI g s0 A m c k u) ?_ c s ⟨0, by omega, positive, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (halfBody_ok hu (by omega) bound) fun t ⟨ht, zt⟩ => ?_
  by_cases last : k + 1 = c
  · left
    refine ⟨?_, last ▸ ht⟩
    change t.zf.map (!·) = some false
    simp [zt, last]
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show c - (k + 1) ≠ 0 from by omega]

end VG.Proof.Rsa.X86.Recover
