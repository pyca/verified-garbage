module

public import VerifiedGarbage.Impl.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Endian conversion has no data-dependent branches or addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86

def reverseTaint : VG.X86.Taint.T :=
  { regs := .ofList [.ebx, .esi, .ecx, .edi, .esp], flags := false }

def reverseEndTaint : VG.X86.Taint.T :=
  { reverseTaint with flags := true }

theorem reverseBytes_check :
    VG.Taint.check taint reverseTaint reverseBytes (.loop reverseTaint (.block [])) =
      some reverseEndTaint := by rfl

/-- Source and destination addresses and the length are public; bytes may
be secret. The conversion has the same trace for every byte string. -/
theorem reverseBytes_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree reverseTaint) reverseBytes := by
  refine VG.Taint.constantTime (A := taint) reverseTaint (fun _ _ _ _ h => h)
    (hc := .loop reverseTaint (.block [])) ?_
  rw [reverseBytes_check]
  rfl

end VG.Proof.Bignum.X86
