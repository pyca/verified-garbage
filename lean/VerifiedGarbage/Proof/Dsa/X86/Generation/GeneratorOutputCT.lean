module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
public meta import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccessCT
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccessCT

/-! # Generator serialization and publication use public pointers and status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure GeneratorOutputPublic where
  frame : PublicFrame
  workspace : BitVec 32
  status : BitVec 32

def GeneratorStoreAt (p : GeneratorOutputPublic) (s : State) : Prop :=
  FrameAt [5] p.frame s ∧ s.gpr .edi = p.workspace

theorem generatorStore_ct (len : Nat) : RelCT isa (Two GeneratorStoreAt)
    (generatorStore len) (fun _ _ => True) := by
  unfold generatorStore
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .edi = p.workspace ∧
    s.gpr .esi = generatorOutputPointer (p.frame.words 5)) [.esp] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht
    exact frameAt_pins _ p.frame s t hs.1 ht.1
  · intro p s R
    refine WP.mono (bufferPointer_ok R.1.1 (R.1.2 5 (by simp)) .esi _) fun t ⟨si, _, K⟩ => ?_
    exact ⟨(K.1 _ (by decide)).trans R.2, si⟩
  · unfold storePublic
    refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_
      ((storeComponent_relCT _ _).mono (fun _ _ h => h) (fun _ _ _ => trivial))
    refine (by exact checkedBlockInvariant rfl rfl : RelCT isa (VG.X86.Taint.Agree (workspaceTaint true))
      (.block [.mov .ecx (.imm (BitVec.allOnes 32))]) (VG.X86.Taint.Agree (workspaceTaint true))).mono ?_ (fun _ _ h => h)
    rintro s t ⟨p, hs, ht⟩
    apply agree_regs
    intro r hr
    have cases : r = .edi ∨ r = .esi := by simpa [workspaceTaint] using hr
    rcases cases with rfl | rfl
    exacts [hs.1.trans ht.1.symm, hs.2.trans ht.2.symm]

def GeneratorOutputAt (p : GeneratorOutputPublic) (s : State) : Prop :=
  GeneratorStoreAt p s ∧ s.mem.readW (off p.frame.base 76) 32 = p.status

theorem generatorPublish_ct (len : Nat) : RelCT isa (Two GeneratorOutputAt)
    (onSuccess (generatorStore len)) (fun _ _ => True) := by
  refine onSuccess_ct (fun p => p.frame.base) GeneratorOutputPublic.status
    (fun _ _ R => ⟨R.1.1.1, R.2⟩) ?_ ?_
  · intro p s t R mem K
    exact ⟨⟨R.1.1.keep mem K (by decide), (K.1 _ (by decide)).trans R.1.2⟩, by rw [mem]; exact R.2⟩
  · exact (generatorStore_ct len).mono (fun _ _ => two_mono (fun _ _ h => h.1.1)) (fun _ _ h => h)

theorem generatorOutput_ct (len : Nat) : RelCT isa
    (Two fun p s => GeneratorStoreAt p s ∧ s.gpr .eax = p.status)
    (.seq (.block [.store (frameSlot 19) .eax]) (onSuccess (generatorStore len))) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := GeneratorOutputAt) [.esp] ?_ (by taint_decide) ?_)
    (generatorPublish_ct len)
  · intro p s t hs ht
    exact frameAt_pins _ p.frame s t hs.1.1 ht.1.1
  · intro p s R
    refine WP.mono (frameStatusAx_ok R.1.1.1 (observedWords_rep p.frame.base s)) fun t ⟨F, W, _, K⟩ => ?_
    refine ⟨⟨⟨F, ?_⟩, (K.1 _ (by simp)).trans R.1.2⟩, ?_⟩
    · intro i hi
      obtain rfl := List.mem_singleton.mp hi
      exact (W 5 (by decide)).trans (R.1.1.2 5 (by simp))
    · exact (W 19 (by decide)).trans R.2
end VG.Proof.Dsa.X86.Generation
