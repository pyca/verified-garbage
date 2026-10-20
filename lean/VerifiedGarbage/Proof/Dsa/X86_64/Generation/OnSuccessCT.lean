module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Framework.OmegaLit

/-! # Phase gates branch only on the public generation status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64

def PhaseDecided {α : Type} (Φ : α → State → Prop) (status : α → BitVec 64)
    (p : α) (s : State) : Prop := Φ p s ∧ isa.eval .e s = some (status p == 1)

theorem onSuccess_ct {α : Type} {Φ : α → State → Prop}
    (context : α → GenerationContext) (status : α → BitVec 64)
    (view : ∀ p s, Φ p s → ∃ W, GenerationMemory (context p) W s ∧ W 19 = status p)
    (stable : ∀ p s t, Φ p s → t.mem = s.mem → Keep [.rax] s t → Φ p t)
    {next : Prog isa}
    (body : RelCT isa (Two fun p s => Φ p s ∧ status p = 1) next (fun _ _ => True)) :
    RelCT isa (Two Φ) (Impl.Dsa.X86_64.Generation.onSuccess next) (fun _ _ => True) := by
  have check : RelCT isa (Two Φ) (.block Impl.Dsa.X86_64.Generation.successStatus)
      (Two (PhaseDecided Φ status)) := by
    refine two_piece [.rsp] ?_ (by taint_decide) ?_
    · intro p s t hs ht r hr
      obtain rfl := List.mem_singleton.mp hr
      obtain ⟨Ws, hms, _⟩ := view p s hs
      obtain ⟨Wt, hmt, _⟩ := view p t ht
      exact hms.layout.rsp.trans hmt.layout.rsp.symm
    · intro p s hs
      obtain ⟨W, hm, hw⟩ := view p s hs
      obtain ⟨V, R⟩ := hm.rep
      refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
      exact ⟨stable p s t hs he hk, by simp only [eval, hz, hw]⟩
  refine RelCT.seq check (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · exact two_map (fun p : α => p) (fun _ _ h => ⟨h.1.1, by
      have he := h.1.2.symm.trans h.2
      exact beq_iff_eq.mp (Option.some.inj he)⟩) body
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
