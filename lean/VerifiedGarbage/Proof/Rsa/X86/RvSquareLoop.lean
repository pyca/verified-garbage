module

public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep

/-! # The public bound on the masked squaring search -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa (sqIter)

theorem sqLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m 0 c st s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (ht : V sTc ≤ c) (count : 0 < c) (limit : c ≤ 16384) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.sqBody .ne) s fun t =>
      SI g s0 A AW V m c 0 (sqIter m (V sTc) c st) t := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = c ∧ 0 < j ∧
      SI g s0 A AW V m k (c - k) (sqIter m (V sTc) k st) u)
    ?_ c s ⟨0, by omega, count, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (sqBody_step hu value bound inverse odd hm one neg
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨hs, zt⟩ => ?_
  have next : SI g s0 A AW V m (k + 1) (c - (k + 1)) (sqIter m (V sTc) (k + 1) st) t := by
    simpa only [sqIter, Nat.sub_sub] using hs
  by_cases last : k + 1 = c
  · left
    refine ⟨?_, ?_⟩
    · change t.zf.map (!·) = some false
      simp [zt, show c - k - 1 = 0 by omega]
    · simpa only [last, Nat.sub_self] using next
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, next⟩
    change t.zf.map (!·) = some true
    simp [zt, show c - k - 1 ≠ 0 by omega]

end VG.Proof.Rsa.X86.Recover
