module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The lowest-word scan visits every public pair without secret control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.LowPair

theorem step_trace (src index : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (step src index))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (step src index)) (.block (step 0 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

theorem steps_trace (src start count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (steps src start count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  induction count generalizing start with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ count ih => exact RelCT.seq (step_trace src start) (ih (start + 1))

theorem scan_trace (src count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (scan src count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (checkedBlockInvariant (τ' := roundTaint [.edi, .ebx, .esi]) rfl rfl) (steps_trace src 0 count)

end VG.Proof.RsaKeyGen.X86.LowPair
