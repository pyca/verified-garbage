module

public import VerifiedGarbage.Proof.Rsa.X86.RvExpInvariant

/-! # The fixed-length exponentiation loop for one recovery candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Recover

theorem expLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m b r c : Nat}
    (h : EI g s0 A AW V m b r c 0 s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (positive : 0 < m) (one : A aO = 2 ^ (64 * g.n) % m)
    (count : 0 < c) (limit : c ≤ 16384) :
    WP isa (.loop (expBody g.n) .ne) s (EI g s0 A AW V m b r c c) := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = c ∧ 0 < j ∧ EI g s0 A AW V m b r c k u)
    ?_ c s ⟨0, by omega, count, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (expBody_ok hu value bound inverse odd positive one (by omega) limit)
    fun t ⟨ht, zt⟩ => ?_
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
