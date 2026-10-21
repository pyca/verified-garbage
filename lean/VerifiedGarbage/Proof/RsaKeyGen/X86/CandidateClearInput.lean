module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClear
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateGeometry
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment

/-! # Clearing the output retains every input needed by the candidate body -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem clear_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateClear.code s fun t =>
      Input E eBytes pBytes entropy t ∧
      Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0 ∧
      MutableFrame E s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthPositive : 0 < E.length := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  have lengthBound : E.length < 2 ^ 32 := CandidateGeometry.native_length_bound v.length
  refine WP.mono_syms (CandidateClear.code_ok I.scratch (by omega) lengthPositive lengthBound I.out_eq
    (I.header 1 (by decide)) v.outFit I.outWrite) fun t ⟨zeros, _, O, K⟩ syms => ?_
  have F : Frame [E.outRegion] s.mem t.mem := by
    simpa only [Environment.outRegion, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame O (by omega)
  have M : MutableFrame E s.mem t.mem :=
    F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_append_left _ List.mem_cons_self)
  have readHeader (d : Nat) (fit : d + 4 ≤ E.size) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    F.readW (r := E.workspaceRegion) (Offset.contains_base _ fit (by have := I.scratch.nowrap; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.outWorkspace.symm) (by decide)
  refine ⟨I.keepMutable v K (by decide) (by decide) M ?_ ?_ (by rw [syms]), zeros, M, K⟩
  · intro i index
    exact (readHeader _ (by omega)).trans (I.header i index)
  · exact (readHeader 44 (by omega)).trans I.usedPointer

end VG.Proof.RsaKeyGen.X86.Candidate
