module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Phase gates branch only on the public generation status -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64

def PhaseDecided {α : Type} (Φ : α → State → Prop) (status : α → BitVec 64)
    (p : α) (s : State) : Prop := Φ p s ∧ isa.eval (.zero .x .x3) s = some (status p == (1#64))

/-- The gate, for states whose frame holds the status. -/
theorem onSuccess_ct_of {α : Type} {Φ : α → State → Prop} (status : α → BitVec 64)
    (view : ∀ p s, Φ p s → ∃ F S V W, Lay s F S ∧ Rep s.mem F S V W ∧ W 19 = status p)
    (stable : ∀ p s t, Φ p s → t.mem = s.mem → Keep [.x3, .x4] s t → Φ p t)
    {next : Prog isa}
    (body : RelCT isa (Two fun p s => Φ p s ∧ status p = 1) next (fun _ _ => True)) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.onSuccess next) (fun _ _ => True) := by
  have check : RelCT isa (Two Φ) (.block Impl.Dsa.AArch64.Generation.successStatus)
      (Two (PhaseDecided Φ status)) := by
    refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_
    intro p s hs
    obtain ⟨F, S, V, W, L, R, hw⟩ := view p s hs
    refine WP.mono (successStatus_ok L R) fun t ⟨hz, he, hk⟩ => ?_
    exact ⟨stable p s t hs he hk, by simpa only [hw] using hz⟩
  refine RelCT.seq check (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · exact two_map (fun p : α => p) (fun _ _ h => ⟨h.1.1, by
      have he := h.1.2.symm.trans h.2
      exact beq_iff_eq.mp (Option.some.inj he)⟩) body
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)

theorem onSuccess_ct {α : Type} {Φ : α → State → Prop}
    (context : α → GenerationContext) (status : α → BitVec 64)
    (view : ∀ p s, Φ p s → ∃ W, GenerationMemory (context p) W s ∧ W 19 = status p)
    (stable : ∀ p s t, Φ p s → t.mem = s.mem → Keep [.x3, .x4] s t → Φ p t)
    {next : Prog isa}
    (body : RelCT isa (Two fun p s => Φ p s ∧ status p = 1) next (fun _ _ => True)) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.onSuccess next) (fun _ _ => True) :=
  onSuccess_ct_of status (fun p s hs => by
    obtain ⟨W, hm, hw⟩ := view p s hs
    obtain ⟨V, R⟩ := hm.rep
    exact ⟨_, _, V, W, hm.layout, R, hw⟩) stable body

end VG.Proof.Dsa.AArch64.Generation
