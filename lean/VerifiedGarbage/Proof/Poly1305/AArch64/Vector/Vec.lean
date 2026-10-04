import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Finish

/-!
# Poly1305 on AArch64 in AdvSIMD: `vec`

Untrusted: everything here is checked by Lean. From at least 128 bytes of
data at `x2` (`x3` of them), `vec` absorbs the first `64 ⌊x3 / 64⌋` into the
accumulator `x4:x5:x6` (`VEnd`).
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector

theorem vec_ok {s₀ : State} {R : Nat} (hk : Radix64.Keys R s₀) (hn : 128 ≤ (s₀.gpr .x3).toNat)
    (hw : ∀ k < 7, InRegions s₀.wr (svA (s₀.gpr .x0) k) 8)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa vec s₀ fun t => ∃ M, Saved s₀ M ∧ VEnd s₀ R M t := by
  have hq : 2 ≤ nq s₀ := by simp only [nq]; omega
  have hw' : ∀ k < 7, InRegions (s₀.rd ++ s₀.wr) (svA (s₀.gpr .x0) k) 8 := fun k hk => by
    obtain ⟨r, hr, hc⟩ := hw k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (setup_ok hk hn hw) fun s1 ⟨yL, yF, M, hY, hS, hL⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hY hL hq hd) fun s2 h2 =>
    WP.mono (finish_ok hY hS h2 hq hd hw') fun t ht => ⟨M, hS, ht⟩)

end VG.Proof.Poly1305.AArch64.Vector
