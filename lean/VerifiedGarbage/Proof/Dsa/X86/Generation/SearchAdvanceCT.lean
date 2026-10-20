module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchAdvance
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControl

/-! # The p-search limit branch depends only on its public attempt counter -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

structure SearchControlPublic where
  base : Addr
  counter : Nat
  stride : Nat

def SearchAdvanceAt (limit : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchControl p.base p.counter p.stride s ∧ p.counter < limit ∧ limit ≤ 12288

theorem searchAdvance_ct (limit : Nat) (stride : Nat) : RelCT isa
    (Two fun p s => SearchAdvanceAt limit p s ∧ p.stride = stride)
    (pSearchAdvance limit stride) (fun _ _ => True) := by
  unfold pSearchAdvance
  refine RelCT.seq (two_piece (Ψ := fun p s => (s.gpr .edi).toNat = p.base.toNat ∧
    s.cf = some (decide (p.counter + 1 < limit))) [.edi] ?_ (hc := .block []) ?_ ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.1.scr.edi_toNat.trans ht.1.1.scr.edi_toNat.symm)
  · exact (congrArg Option.isSome (check_of_erase_eq (.block (pSearchAdvanceHead limit stride))
      (.block (pSearchAdvanceHead 1 1)) (τr [.edi]) (.block []) rfl rfl rfl)).trans (by rfl)
  · rintro p s ⟨⟨R, hc, hl⟩, strideEq⟩
    refine WP.mono (pSearchAdvanceHead_ok R.scr (by decide) (by omega) (by omega) R.count R.offset)
      fun t ⟨_, _, cf, _, K⟩ => ?_
    exact ⟨by rw [K.1 _ (by decide)]; exact R.scr.edi_toNat, cf⟩
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    all_goals
      refine two_taint [.edi] ?_ (by taint_decide)
      intro p s t hs ht r hr
      obtain rfl := List.mem_singleton.mp hr
      exact BitVec.eq_of_toNat_eq (hs.1.1.trans ht.1.1.symm)
end VG.Proof.Dsa.X86.Generation
