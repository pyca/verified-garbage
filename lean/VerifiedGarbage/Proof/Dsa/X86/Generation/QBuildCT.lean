module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.QCandidateCT
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.QCandidateCT

/-! # Loading a candidate's public pointers does not publish unrelated frame words -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

def qHashPublic (p : PublicFrame) : HashPublic :=
  ⟨p.words 1, p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q, p.words 14, p.base.setWidth 32⟩

def QBuildAt {H : Hash} (K : HashOK H) (len : Nat) (p : PublicFrame) (s : State) : Prop :=
  FrameAt [1, 5, 14] p s ∧ HashResources K (qHashPublic p).input (qHashPublic p).output (qHashPublic p).scratch len s

theorem qBuild_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (QBuildAt K len)) (qBuild H len) (fun _ _ => True) := by
  unfold qBuild
  refine RelCT.seq (two_piece (Ψ := fun p => HashAt K len (qHashPublic p)) [.esp] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht
    exact frameAt_pins _ p s t hs.1 ht.1
  · intro p s R
    refine WP.mono (qHashArgs_ok R.1.1 (observedWords_rep p.base s)) fun t ⟨si, di, bp, _, Kt⟩ => ?_
    refine ⟨R.2.keeps Kt (by decide), ?_, ?_, ?_, ?_⟩
    · change t.gpr .esp = p.base.setWidth 32
      rw [Kt.1 _ (by decide), ← R.1.1.esp]
      simp
    · exact si.trans (R.1.2 1 (by simp))
    · exact di.trans (congrArg (· + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q) (R.1.2 5 (by simp)))
    · exact bp.trans (R.1.2 14 (by simp))
  · exact two_map qHashPublic (fun _ _ h => h) (qCandidate_ct K len)
end VG.Proof.Dsa.X86.Generation
