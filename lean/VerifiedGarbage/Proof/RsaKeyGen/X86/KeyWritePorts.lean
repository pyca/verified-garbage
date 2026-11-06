module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Export all seven key components without losing earlier outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportProgress (g : OutputGeometry) (m : Mem) (accept : Bool) (i : Nat) (s : State) : Prop where
  input : OutputInput g s
  zero : num s.mem g.base g.n aZero = 0
  mask : slot s.mem g.base kOk = if accept then 1 else 0
  header : ∀ d, d + 4 ≤ hdr → slot s.mem g.base d = slot m g.base d
  pending : ∀ j, i ≤ j → j < 7 → num s.mem g.base g.n (outputIndex j) = num m g.base g.n (outputIndex j)
  done : ∀ j, j < i → j < 7 → Spec.Rsa.bytesAt s.mem (g.region j).base (g.region j).len = portResult g m accept j

end VG.Proof.RsaKeyGen.X86.Key
