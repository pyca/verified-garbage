module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunPost
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunPost
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Complete groups iterate a public number of times. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (groupBody expGroups)

theorem groups_loop_ct (W : Window) :
    RelCT isa (Two fun p s => 0 < p.len/5 ∧ RunInv p 0 0 s)
      (.loop (groupBody W.code) (.nonzero .x .x9)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun p j => RunInv p (5*j) 0) (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (fun p : RunPub => p.len/5) ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : RunPub × Nat => (p.1,5*p.2))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (groupBody_ct W)
  · intro p j s hj hs
    refine WP.mono (hs.groupStep W (by omega)) fun t ⟨ht,h9⟩ => ?_
    have hnext : RunInv p (5*(j+1)) 0 t := by simpa only [Nat.mul_add,Nat.mul_one] using ht
    refine ⟨?_,fun _ => hnext,fun he => by simpa only [he] using hnext⟩
    change some (!(t.gpr .x9 == 0)) = some (decide (j+1 < p.len/5))
    rw [h9]
    by_cases he : 5*j+10 ≤ p.len
    · simp only [he,ite_true,show j+1 < p.len/5 by omega,decide_true]; rfl
    · simp only [he,ite_false,show ¬ j+1 < p.len/5 by omega,decide_false]; rfl

def GroupsReady (p : RunPub) (s : State) : Prop :=
  RunInv p 0 0 s ∧ s.gpr .x9 = if 5 ≤ p.len then 1 else 0

theorem expGroups_ct (W : Window) :
    RelCT isa (Two fun p => RunInv p 0 0) (expGroups W.code) (fun _ _ => True) := by
  unfold expGroups
  refine RelCT.seq (two_post (Ψ := GroupsReady)
    (x0_ct (fun p : RunPub => off p.ws.B p.ws.o) (fun _ _ h => h.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.haveFive (Nat.zero_le _)) fun _ ht => ⟨ht.1,by simpa only [Nat.zero_add] using ht.2⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x9 == 0)) = some (!(t.gpr .x9 == 0))
    rw [hs.2,ht.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.len/5
      by_contra hz
      have hn : ¬ 5 ≤ p.len := by omega
      change some (!(s.gpr .x9 == 0)) = some true at he
      rw [hs.2,ite_eq_right hn] at he
      contradiction,hs.1⟩) (groups_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive
