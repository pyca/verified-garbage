module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap

/-! # Each masked output retains the header, zero array and validity bit for the next port -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportState (E : Environment) (s : State) : Prop where
  input : Input E s
  zero : num s.mem E.base E.n aZero = 0
  bit : slot s.mem E.base kOk ≤ 1

end VG.Proof.RsaKeyGen.X86.Key
