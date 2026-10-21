module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext

/-! # Complete workspace import from the original big-endian input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Import

theorem load_ok {g : Geometry} {s : State} {out : Nat} (C : Context g s)
    (source : s.gpr .esi = g.src) (destination : s.gpr .edi + BitVec.ofNat 32 out = g.dst) :
    WP isa (load g.count out) s fun t =>
      (t.mem.read (g.dst.setWidth 64) (4 * g.count)).toNat =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.src.setWidth 64) (4 * g.count)) ∧
      Frame [g.destRegion] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.seq (WP.mono (args_ok source destination) fun a ⟨M, K, Ps, Pd, Pc⟩ => ?_)
  have Ca : Context g a := ⟨C.positive, C.sourceFit, C.destFit,
    fun i index => by rw [K.2.1, K.2.2]; exact C.readable i index,
    fun i index => by rw [K.2.2]; exact C.writable i index, C.separate⟩
  refine WP.mono (code_ok Ca Ps Pd Pc) fun t T => ?_
  have value := T.os2ip
  have frame := T.frame
  rw [M] at value frame
  exact ⟨value, frame, (K.mono (by decide)).trans T.keeps⟩

end VG.Proof.RsaKeyGen.X86.Import
