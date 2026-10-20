module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeControl
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Whole-draw availability is determined by public tape length and consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

def PrimeCheckedAt (G : PrimeConfig) (p : PrimeLoopPublic G) (s : State) : Prop :=
  PrimeLoopAt G p s ∧ s.cf = some (decide (G.tapeLen - p.used < G.draw))

theorem primeTapeCheck_ct (G : PrimeConfig) : RelCT isa (Two (PrimeLoopAt G))
    (.block (primeTapeCheck G.draw)) (Two (PrimeCheckedAt G)) := by
  refine two_piece [.edi] ?_ (hc := .block []) (by rfl) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.ready.context.scr.edi_toNat.trans ht.ready.context.scr.edi_toNat.symm)
  · intro p s R
    have room : primeTapeLen + 4 ≤ G.size := by have := G.flagRoom; unfold primeTapeLen primeIsUniform at *; omega
    have draw32 : G.draw < 2 ^ 32 := by have := G.width; unfold PrimeConfig.draw; omega
    refine WP.mono (primeTapeCheck_ok R.ready.context.scr room p.usedBound G.tapeLen32 draw32 R.ready.tapeLen R.used)
      fun t ⟨cf, mem, K⟩ => ?_
    exact ⟨R.keep mem K (by decide) (by decide), cf⟩
end VG.Proof.Dsa.X86.Generation
