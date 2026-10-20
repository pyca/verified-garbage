module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchTailCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchAdvance

/-! # The controller tail preserves payload memory and exposes the public retry flag -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def SearchTailPublic.nextCounter (p : SearchTailPublic) : Nat :=
  if p.status = 3 then p.control.counter + 1 else p.control.counter

def SearchTailPublic.nextStatus (p : SearchTailPublic) (limit : Nat) : Nat :=
  if p.status = 3 then if p.control.counter + 1 < limit then 3 else 2 else p.status

theorem searchTail_result {limit stride : Nat} {p : SearchTailPublic} {s : State}
    (H : SearchTailAt limit stride p s) : WP isa (searchTail limit stride) s fun t =>
      SearchControl p.control.base p.nextCounter stride t ∧
      t.zf = some (decide (p.nextStatus limit = 3)) ∧
      Outside p.control.base 0 12 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold searchTail
  refine WP.seq (WP.mono (pSearchStatusCmp_ok H.1.1 H.2.2.1 H.2.2.2) fun a ⟨zf, mem, K⟩ => ?_)
  have Ca : SearchControl p.control.base p.control.counter stride a := by
    rw [← H.2.1]
    exact H.1.1.unchanged mem K (by decide) (by decide)
  by_cases retry : p.status = 3
  · refine WP.seq (WP.ite true (by change a.zf = some true; simp only [zf, retry, decide_true])
      (fun _ => ?_) (fun he => Bool.noConfusion he))
    refine WP.mono (pSearchAdvance_ok Ca H.1.2.1 H.1.2.2) fun b ⟨Cb, status, O, Kb⟩ => ?_
    refine WP.mono (pSearchStatusCmp_ok Cb (by split <;> decide) status) fun t ⟨zt, mt, Kt⟩ => ?_
    refine ⟨?_, ?_, ?_, (K.mono (by decide)).trans (Kb.trans (Kt.mono (by decide)))⟩
    · simpa only [SearchTailPublic.nextCounter, retry, ite_true] using Cb.unchanged mt Kt (by decide) (by decide)
    · simpa only [SearchTailPublic.nextStatus, retry, ite_true] using zt
    · rw [mt, ← mem]; exact O
  · refine WP.seq (WP.ite false (by change a.zf = some false; simp only [zf, retry, decide_false])
      (fun he => Bool.noConfusion he) (fun _ => WP.block_nil ?_))
    refine WP.mono (pSearchStatusCmp_ok Ca H.2.2.1 (by rw [mem]; exact H.2.2.2)) fun t ⟨zt, mt, Kt⟩ => ?_
    refine ⟨?_, ?_, ?_, (K.mono (by decide)).trans (Kt.mono (by decide))⟩
    · simpa only [SearchTailPublic.nextCounter, ite_eq_right retry] using Ca.unchanged mt Kt (by decide) (by decide)
    · simpa only [SearchTailPublic.nextStatus, ite_eq_right retry] using zt
    · rw [mt, mem]; exact Outside.refl _ _ _ _
end VG.Proof.Dsa.X86.Generation
