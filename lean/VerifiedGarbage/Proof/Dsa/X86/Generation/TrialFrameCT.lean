module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCheckCT
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialInputsKeep
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCheckCT

/-! # Trial division obtains its public source and table from the persistent frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure TrialBridgePublic where
  frame : PublicFrame
  stack : Addr
  value : Nat

def trialBridgeCall (p : TrialBridgePublic) : TrialPublic :=
  ⟨p.stack, p.frame.words 22, p.frame.words 5, p.value, 0⟩

def TrialBridgeAt (len entries : Nat) (p : TrialBridgePublic) (s : State) : Prop :=
  FrameAt [5, 22] p.frame s ∧ 16 ≤ (s.gpr .esp).toNat ∧
    TrialInputs (allocated 16 s) p.stack (p.frame.words 22) (p.frame.words 5) len entries ∧
    trialValue s (p.frame.words 22) len = p.value

theorem trialFromFrame_ct (len : Nat) : RelCT isa (Two (TrialBridgeAt len (if len ≤ 128 then 512 else 1024)))
    (trialFromFrame len) (fun _ _ => True) := by
  unfold trialFromFrame
  refine RelCT.seq (two_piece (Ψ := fun p => TrialCallAt len (if len ≤ 128 then 512 else 1024) (trialBridgeCall p))
    [.esp] ?_ (by taint_decide) ?_)
    (two_map trialBridgeCall (fun _ _ h => h) (trialCheck_ct _ _))
  · intro p s t hs ht
    exact frameAt_pins _ p.frame s t hs.1 ht.1
  · intro p s R
    refine WP.mono (trialArgs_ok R.1.1 (observedWords_rep p.frame.base s)) fun t ⟨si, di, mem, K⟩ => ?_
    refine ⟨by rw [K.1 _ (by decide)]; exact R.2.1,
      R.2.2.1.keep mem (keeps_allocated K (by decide) 16) (by decide), ?_, ?_, ?_⟩
    · change trialValue t (p.frame.words 22) len = p.value
      unfold trialValue; rw [mem]; exact R.2.2.2
    · exact si.trans (R.1.2 22 (by simp))
    · exact di.trans (R.1.2 5 (by simp))
end VG.Proof.Dsa.X86.Generation
