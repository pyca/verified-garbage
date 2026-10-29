module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext

import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Complete workspace import from the original big-endian input -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ImportEntry.lean`, which only this module imported.
section

/-! # Install the native import pointers and public iteration count -/

section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Import

theorem args_ok {g : Geometry} {s : State} {out : Nat}
    (source : s.gpr .esi = g.src) (destination : s.gpr .edi + BitVec.ofNat 32 out = g.dst) :
    WP isa (.block (args g.count out)) s fun t =>
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t ∧
      t.gpr .esi = g.sourcePtr 0 ∧ t.gpr .ebx = g.destPtr 0 ∧
      t.gpr .ecx = BitVec.ofNat 32 g.count := by
  unfold args
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ecx] s t := ((A.keeps.mono (by decide)).widen B.keeps).widen T.keeps
  refine ⟨T.mem.trans (B.mem.trans A.mem), K, ?_, ?_, T.gpr⟩
  · rw [K.1 .esi (by decide), source]
    simp only [Geometry.sourcePtr, Nat.mul_zero, BitVec.add_zero]
  · rw [T.other .ebx (by decide), B.gpr, A.gpr]
    unfold Geometry.destPtr
    rw [Nat.mul_zero]
    change _ = g.dst + BitVec.ofNat 32 (4 * (g.count - 1)) - 0#32
    rw [BitVec.sub_zero, ← destination, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.RsaKeyGen.X86.Import
end

end

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
