module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # Encoding and comparison disclose only public lengths and addresses -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86

def encodeTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .ecx, .edx, .esi, .ebp], flags := false }

theorem encode_relCT : RelCT isa (VG.X86.Taint.Agree encodeTaint)
    VG.Impl.RsaPkcs1Sig.X86.encode (fun _ _ => True) := by
  apply RelCT.taint (A := taint) encodeTaint (fun _ _ h => h)
  taint_decide

def compareTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esi, .ecx], flags := false }

theorem compare_relCT : RelCT isa (VG.X86.Taint.Agree compareTaint) compare (fun _ _ => True) := by
  apply RelCT.taint (A := taint) compareTaint (fun _ _ h => h)
  taint_decide

end VG.Proof.RsaPkcs1Sig.X86
