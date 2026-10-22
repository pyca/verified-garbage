module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Short R² preparation preserves the caller's public stack and workspace base -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.RsaKeyGen.X86.FastR2

theorem seedAt_round_trace (n e out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (seedAt n e out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold seedAt setConstW
  refine RelCT.seq (erased_relCT (σ := roundTaint [.edi]) _ (zerosW 0 1)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (zerosW 0 1))) rfl rfl rfl rfl) ?_
  apply blockFlatMap_relCT
  intro j
  split
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact erased_relCT _ (.block [.mov .eax (.imm 1), .store (sc 0) .eax])
      (.block []) rfl rfl rfl rfl

theorem seed_round_trace (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (seed n out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  seedAt_round_trace n _ out

theorem doublesAt_round_trace (M : VG.Impl.Mont.Mod) (e acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (doublesAt M e acc out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine RelCT.seq (seedAt_round_trace _ _ _) ?_
  let reference : Prog isa := .seq (.block [.mov .esi (.imm 1)])
    (doubleLoop { n := 1, mo := 0, tmp := 0, minv := 0 } 0 0)
  exact erased_relCT (τ := roundTaint [.edi]) (σ := roundTaint [.edi])
    (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (M.n + 64 * M.n - e)))]) (doubleLoop M acc out))
    reference (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase reference))
    rfl rfl rfl (by decide +kernel)

theorem doubles_round_trace (M : VG.Impl.Mont.Mod) (acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (doubles M acc out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  doublesAt_round_trace M _ acc out

end VG.Proof.RsaKeyGen.X86.FastR2
