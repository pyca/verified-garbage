module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchAdvanceCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchAdvance

/-! # Public status gates counter advancement and the next loop test -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure SearchTailPublic where
  control : SearchControlPublic
  status : Nat

def SearchTailAt (limit stride : Nat) (p : SearchTailPublic) (s : State) : Prop :=
  SearchAdvanceAt limit p.control s ∧ p.control.stride = stride ∧ p.status ≤ 3 ∧
    s.mem.readW (off p.control.base 8) 32 = BitVec.ofNat 32 p.status

def SearchTailChecked (limit stride : Nat) (p : SearchTailPublic) (s : State) : Prop :=
  SearchTailAt limit stride p s ∧ s.zf = some (decide (p.status = 3))

def searchTail (limit stride : Nat) : Prog isa :=
  .seq (.block pSearchStatusCmp)
    (.seq (.ite .e (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp))

theorem searchStatus_ct (limit stride : Nat) : RelCT isa (Two (SearchTailAt limit stride))
    (.block pSearchStatusCmp) (Two (SearchTailChecked limit stride)) := by
  refine two_piece [.edi] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.1.scr.edi_toNat.trans ht.1.1.scr.edi_toNat.symm)
  · intro p s R
    refine WP.mono (pSearchStatusCmp_ok R.1.1 R.2.2.1 R.2.2.2) fun t ⟨zf, mem, K⟩ => ?_
    exact ⟨⟨⟨R.1.1.unchanged mem K (by decide) (by decide), R.1.2⟩, R.2.1, R.2.2.1, by rw [mem]; exact R.2.2.2⟩, zf⟩

theorem searchTailBranch_ct (limit stride : Nat) : RelCT isa (Two (SearchTailChecked limit stride))
    (.ite .e (pSearchAdvance limit stride) (.block [])) (fun _ _ => True) := by
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · exact two_map (fun p => p.control) (fun _ _ h => ⟨h.1.1.1, h.1.1.2.1⟩) (searchAdvance_ct limit stride)
  · exact RelCT.nil (fun _ _ _ => trivial)

theorem searchTail_ct (limit stride : Nat) : RelCT isa (Two (SearchTailAt limit stride))
    (searchTail limit stride) (fun _ _ => True) := by
  refine RelCT.seq (searchStatus_ct limit stride) (RelCT.seq
    (two_post (Ψ := fun p s => (s.gpr .edi).toNat = p.control.base.toNat) (searchTailBranch_ct limit stride) ?_) ?_)
  · intro p s H
    by_cases retry : p.status = 3
    · refine WP.ite true (by change s.zf = some true; simp only [H.2, retry, decide_true])
        (fun _ => ?_) (fun he => Bool.noConfusion he)
      have C : SearchControl p.control.base p.control.counter stride s := by rw [← H.1.2.1]; exact H.1.1.1
      exact WP.mono (pSearchAdvance_ok C H.1.1.2.1 H.1.1.2.2) fun _ ⟨R, _, _, _⟩ => R.scr.edi_toNat
    · exact WP.ite false (by change s.zf = some false; simp only [H.2, retry, decide_false])
        (fun he => Bool.noConfusion he) (fun _ => WP.block_nil H.1.1.1.scr.edi_toNat)
  · refine two_taint [.edi] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.trans ht.symm)
end VG.Proof.Dsa.X86.Generation
