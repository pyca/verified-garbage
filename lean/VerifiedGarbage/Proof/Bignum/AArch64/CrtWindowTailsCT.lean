module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunPost
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunPost
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The trailing-byte loop depends on public length, never exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (tailBody expTail)

theorem tails_loop_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => 0 < p.1.len-p.2 ∧ RunInv p.1 p.2 0 s)
      (.loop (tailBody W.code) (.nonzero .x .x3)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun (p : RunPub × Nat) j => RunInv p.1 (p.2+j) ((8*j)%5))
    (Ψ := fun _ _ => True) (fun p : RunPub × Nat => p.1.len-p.2) ?_ ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : (RunPub × Nat) × Nat => (p.1.1,p.1.2+p.2,(8*p.2)%5))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (tailBody_ct W)
  · intro p j s hj hs
    have hL : p.1.len < 2 ^ 64 := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hL,_⟩ := hs
      exact hL
    refine WP.mono (hs.tailStep W (by omega)) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,?_,fun _ => trivial⟩
    · exact eval_nz_count hj (by rw [h3,cnt_ne (by omega)]; omega)
    · intro _
      have hb : ((8*j)%5+8)%5 = (8*(j+1))%5 := by omega
      simpa only [hb,Nat.add_assoc] using ht

def TailsReady (p : RunPub × Nat) (s : State) : Prop :=
  p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s ∧ s.gpr .x3 = BitVec.ofNat 64 (p.1.len-p.2)

theorem expTail_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s)
      (expTail W.code) (fun _ _ => True) := by
  unfold expTail
  refine RelCT.seq (two_post (Ψ := TailsReady)
    (x0_ct (fun p : RunPub × Nat => off p.1.ws.B p.1.ws.o) (fun _ _ h => h.2.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.2.remaining h.1) fun _ h' => ⟨h.1,h'⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x3 == 0)) = some (!(t.gpr .x3 == 0))
    rw [hs.2.2,ht.2.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.1.len-p.2
      by_contra hz
      have hn : p.1.len-p.2 = 0 := by omega
      change some (!(s.gpr .x3 == 0)) = some true at he
      rw [hs.2.2,hn] at he
      contradiction,hs.2.1⟩) (tails_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive
