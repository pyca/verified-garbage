module

public import VerifiedGarbage.Proof.Bignum.AArch64.FoldedLoop
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum.AArch64

structure PublicData where
  L : Lay
  N : Nat

def Facts (p : PublicData) : Prop :=
  slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2^31 ∧
  Nat.Coprime (2^(64*p.L.w)) p.N

def Inv (p : PublicData) (i : Nat) (s : State) : Prop :=
  ∃ s₀ X x, SquareInv s₀ p.L.B p.L.Z p.L.w p.N X x p.L.minv i s ∧ Facts p

theorem step_ct (M : Mont) :
    RelCT isa (Two fun (q : PublicData × Nat) s => q.2 < 16 ∧ Inv q.1 q.2 s)
      (Folded.squareStep M.mm) (fun _ _ => True) := by
  unfold Folded.squareStep
  refine RelCT.seq (two_post (Ψ := fun (q : PublicData × Nat) t => t.gpr .x0 = q.1.L.B)
    (two_map (fun (q : PublicData × Nat) => q.1.L)
      (fun _ _ ⟨_,_,_,_,h,hf⟩ => ⟨h.ctx.good,hf.1⟩)
      (M.ctL (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide))) ?_)
    (two_taint [.x0] (fun q s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro q s ⟨_,s₀,X,x,h,hf⟩
  exact WP.mono (M.mm_ok h.ctx.good hf.1 hf.2.1 hf.2.2.1 (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.ctx.inv (by rw [h.ctx.n]; exact h.reduced)) fun t ⟨hg,_⟩ => hg.x0

theorem squares_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 16 ∧ Inv p 0 s)
      (.loop (Folded.squareStep M.mm) (.nonzero .x .x3)) (Two fun p s => Inv p 16 s) := by
  refine two_loop (Φ := Inv) (fun _ => 16) (step_ct M) ?_
  rintro p i s hi ⟨s₀,X,x,h,hf⟩
  exact WP.mono (loopStep_ok M hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hi h)
    fun t ⟨hz,ht⟩ => ⟨eval_count_r hi hz, fun _ => ⟨s₀,X,x,ht,hf⟩,
      fun he => he ▸ ⟨s₀,X,x,ht,hf⟩⟩

end VG.Proof.Bignum.AArch64.FoldedPublic
