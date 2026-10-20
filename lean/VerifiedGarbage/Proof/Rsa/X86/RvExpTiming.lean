module

import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvExpInvariant
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Binary exponentiation has the same fixed schedule for different private exponents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Recover

theorem expLoop_relCT (g : Geo) (s0 t0 : State) (A B AW BW V W : Nat → Nat)
    (m b d r q c : Nat)
    (valueA : A mBase = m) (valueB : B mBase = m)
    (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (pos : 0 < m)
    (oneA : A aO = 2 ^ (64 * g.n) % m) (oneB : B aO = 2 ^ (64 * g.n) % m)
    (positive : 0 < c) (limit : c ≤ 16384) :
    RelCT isa (fun s t => EI g s0 A AW V m b r c 0 s ∧ EI g t0 B BW W m d q c 0 t)
      (.loop (expBody g.n) .ne)
      (fun s t => EI g s0 A AW V m b r c c s ∧ EI g t0 B BW W m d q c c t) := by
  apply fixedLoop_relCT (fun k s => EI g s0 A AW V m b r c k s)
    (fun k t => EI g t0 B BW W m d q c k t) positive (expBody_workspace g.n)
  · intro k s t hs ht
    exact ks_agree hs ht
  · intro k s hk hs
    exact expBody_ok hs valueA bound invA odd pos oneA hk limit
  · intro k t hk ht
    exact expBody_ok ht valueB bound invB odd pos oneB hk limit

end VG.Proof.Rsa.X86.Recover
