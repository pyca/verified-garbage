module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep

import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming

/-! # Masked squaring uses a public iteration count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa (sqIter)

theorem sqLoop_relCT (g : Geo) (s0 t0 : State) (A B AW BW V W : Nat → Nat)
    (m c : Nat) (st tt : Nat × Bool × Bool)
    (valueA : A mBase = m) (valueB : B mBase = m)
    (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (large : 1 < m)
    (oneA : A aO = 2 ^ (64 * g.n) % m) (oneB : B aO = 2 ^ (64 * g.n) % m)
    (negA : A aNg = m - 2 ^ (64 * g.n) % m) (negB : B aNg = m - 2 ^ (64 * g.n) % m)
    (tcA : V sTc ≤ c) (tcB : W sTc ≤ c) (positive : 0 < c) (limit : c ≤ 16384) :
    RelCT isa (fun s t => SI g s0 A AW V m 0 c st s ∧ SI g t0 B BW W m 0 c tt t)
      (.loop (sqBody g.n) .ne)
      (fun s t => SI g s0 A AW V m c 0 (sqIter m (V sTc) c st) s ∧
        SI g t0 B BW W m c 0 (sqIter m (W sTc) c tt) t) := by
  have loop := fixedLoop_relCT
    (fun k s => SI g s0 A AW V m k (c - k) (sqIter m (V sTc) k st) s)
    (fun k t => SI g t0 B BW W m k (c - k) (sqIter m (W sTc) k tt) t)
    positive (sqBody_workspace g.n) (fun _ _ _ hs ht => ks_agree hs ht)
    (fun k s hk hs => by
      refine WP.mono (sqBody_step hs valueA bound invA odd large oneA negA
        (by omega) (by omega) (by omega) (by omega)) fun t result => ?_
      simpa only [sqIter, Nat.sub_sub] using result)
    (fun k t hk ht => by
      refine WP.mono (sqBody_step ht valueB bound invB odd large oneB negB
        (by omega) (by omega) (by omega) (by omega)) fun u result => ?_
      simpa only [sqIter, Nat.sub_sub] using result)
  simpa only [sqIter, Function.iterate_zero, id_eq, Nat.sub_zero, Nat.sub_self] using loop

end VG.Proof.Rsa.X86.Recover
