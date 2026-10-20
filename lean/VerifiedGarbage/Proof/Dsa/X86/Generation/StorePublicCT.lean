module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorOutputCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming

/-! # Serialize a candidate component with fixed public buffer addresses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem storePublic_ct (len input : Nat) : RelCT isa (VG.X86.Taint.Agree (workspaceTaint true))
    (storePublic len input) (VG.X86.Taint.Agree (workspaceTaint true)) :=
  RelCT.seq (checkedBlockInvariant rfl rfl) (storeComponent_relCT len input)

theorem bufferPointerStore_ct (len input offset : Nat) : RelCT isa (Two GeneratorStoreAt)
    (.seq (.block (bufferPointer .esi offset)) (storePublic len input)) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .edi = p.workspace ∧
    s.gpr .esi = p.frame.words 5 + BitVec.ofNat 32 offset) [.esp] ?_ (hc := .block []) ?_ ?_) ?_
  · intro p s t hs ht
    exact frameAt_pins _ p.frame s t hs.1 ht.1
  · exact (congrArg Option.isSome (check_of_erase_eq (.block (bufferPointer .esi offset))
      (.block (bufferPointer .esi 0)) (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro p s R
    refine WP.mono (bufferPointer_ok R.1.1 (R.1.2 5 (by simp)) .esi offset) fun t ⟨si, _, K⟩ => ?_
    exact ⟨(K.1 _ (by decide)).trans R.2, si⟩
  · refine (storePublic_ct len input).mono ?_ (fun _ _ _ => trivial)
    rintro s t ⟨p, hs, ht⟩
    apply agree_regs
    intro r hr
    have cases : r = .edi ∨ r = .esi := by simpa [workspaceTaint] using hr
    rcases cases with rfl | rfl
    exacts [hs.1.trans ht.1.symm, hs.2.trans ht.2.symm]
end VG.Proof.Dsa.X86.Generation
