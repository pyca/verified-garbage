module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeCheckCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawRoundCT

/-! # A witness-loop step branches only on public availability and draw results -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem primeAvailable_ct (G : PrimeConfig) : RelCT isa
    (Two fun p s => PrimeCheckedAt G p s ∧ isa.eval .b s = some false)
    (primeDrawRound G.len G.draw G.checks) (Two fun (_ : PrimeLoopPublic G) s => PrimeReady G s) := by
  refine two_post ?_ ?_
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    have fits : ¬ G.tapeLen - p.used < G.draw := by
      simpa only [eval, hs.1.2, Option.some.injEq, decide_eq_false_iff_not] using hs.2
    have full : p.used + G.draw ≤ G.tapeLen := by have := p.usedBound; omega
    exact primeDrawRound_ct G _ _ _ _ _ _ ⟨loopDrawPublic G p full, hs.1.1.draw full, ht.1.1.draw full⟩ es et
  · intro p s h
    have fits : ¬ G.tapeLen - p.used < G.draw := by
      simpa only [eval, h.1.2, Option.some.injEq, decide_eq_false_iff_not] using h.2
    have full : p.used + G.draw ≤ G.tapeLen := by have := p.usedBound; omega
    exact WP.mono (primeDrawRound_ok h.1.1.ready full p.bound h.1.1.used h.1.1.count) fun _ h => h.1

theorem primeStep_ct (G : PrimeConfig) : RelCT isa (Two (PrimeLoopAt G))
    (primeStep G.len G.draw G.checks) (fun _ _ => True) := by
  unfold primeStep
  refine RelCT.seq (primeTapeCheck_ct G) (RelCT.seq (R := Two fun (_ : PrimeLoopPublic G) s => PrimeReady G s) ?_ ?_)
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · refine two_piece [.edi] ?_ (by taint_decide) ?_
      · intro p s t hs ht r hr
        obtain rfl := List.mem_singleton.mp hr
        exact BitVec.eq_of_toNat_eq (hs.1.1.ready.context.scr.edi_toNat.trans ht.1.1.ready.context.scr.edi_toNat.symm)
      · intro p s h
        exact WP.mono (primeMarkReady_ok h.1.1.ready 0) fun _ h => h.1
    · exact primeAvailable_ct G
  · refine two_taint [.edi] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.context.scr.edi_toNat.trans ht.context.scr.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
