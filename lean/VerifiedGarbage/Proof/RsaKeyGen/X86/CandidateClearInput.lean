module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateGeometry
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Clearing the output retains every input needed by the candidate body -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateClear.lean`, which only this module imported.
section

/-! # Output clearing is complete even when candidate entropy is exhausted -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size len : Nat} {out : BitVec 32}
    (S : Scr s base size) (header : 8 ≤ size) (positive : 0 < len) (lengthBound : len < 2 ^ 32)
    (outEq : s.mem.readW (off base 0) 32 = out)
    (lenEq : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 len)
    (fit : out.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (out.setWidth 64) len) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateClear.code s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0#32 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClear.code VG.Impl.RsaKeyGen.X86.CandidateClear.args
  refine WP.seq (wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun c C _ => WP.block_nil ?_)
  have K : Keeps [.esi, .ecx, .eax] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok positive lengthBound fit
    (by rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, outEq])
    (by rw [C.other .ecx (by decide), B.gpr, A.mem, lenEq]) C.gpr ?_) fun t ⟨V, Z, O, T⟩ => ?_
  · intro i index
    rw [K.2.2]
    obtain ⟨r, mem, contains⟩ := write
    exact ⟨r, mem, contains.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · exact ⟨V, Z, M ▸ O, K.trans (T.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.CandidateClear
end

end

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
