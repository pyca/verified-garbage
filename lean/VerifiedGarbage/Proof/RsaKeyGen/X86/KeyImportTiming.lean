module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Native key initialization and prime import reveal only public addresses and widths -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem clearArrays_trace (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (clearArrays n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  exact erased_relCT (clearArrays n) (clearArrays 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (clearArrays 1)) rfl rfl rfl (by rfl)

theorem loadPrime_trace (E : Environment) (i out : Nat) (hi : i < 18) :
    RelCT isa (InputPair E) (loadPrime E.n (4 * i) out)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold loadPrime seqs
  apply RelCT.seq (primeSource_trace E i hi)
  apply RelCT.seq (Import.load_trace (E.n / 2) (slot E.n 0))
  exact (key_public_trace (widenCopy_public E.n (E.n / 2) out (slot E.n 0))).mono
    (fun _ _ P => taint.le_sound (by rfl) P) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Key
