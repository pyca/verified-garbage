module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather

/-! Contiguous seal ABI for the general nonce, AAD, and plaintext lengths. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous

open VG.AArch64

/-- Forward one plaintext descriptor and the independent output address.
Frame offsets 0..23 are the three outgoing arguments, 24..39 the descriptor.
The existing framed record body preserves the incoming link register. -/
def generalArgs : List Instr :=
  [.ldrSp .x9 48, .ldrSp .x10 56, .strSp .x7 0, .strSp .x9 8, .strSp .x10 16,
   .strSp .x6 24, .strSp .x9 32, .addSp .x6 24, .movz .x .x7 1 0]

def generalFrame (v : Calls) : Prog isa :=
  .frame (.alloc 48) (.seq (.block generalArgs) (DirectGather.framed v)) (.free 48)

end VG.Impl.AesGcm.AArch64.Contiguous
