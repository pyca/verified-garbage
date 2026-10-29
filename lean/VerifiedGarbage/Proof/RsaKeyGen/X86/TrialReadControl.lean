module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialPointer
import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialStep
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Only pointers and the fixed word count control a single divisor's trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/TrialControl.lean`, which only this module imported.
section

/-! # Trial-reduction pointer control is independent of candidate arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_control (s : State) (endOffset : Nat) (endPtr : BitVec 32)
    (candidateRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = endPtr) :
    WP isa (.block (wordStep endOffset)) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .ecx, .ebp, .edi] s t ∧ t.gpr .edi = s.gpr .edi + 4 ∧
      t.zf = some (s.gpr .edi + 4 - endPtr == 0) := by
  unfold wordStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS (readSrc_mem rfl candidateRead) fun a A _ => WP.block_nil ?_
  refine WP.mono (redc32_code a) fun b ⟨M, K, _⟩ => ?_
  have Kb : Keeps [.eax, .edx, .ecx, .ebp] s b := (A.keeps.mono (by decide)).trans K
  have Mb : b.mem = s.mem := M.trans A.mem
  refine wp_addS rfl fun c C _ => ?_
  have Kc : Keeps [.eax, .edx, .ecx, .ebp, .edi] s c := (Kb.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have read : readSrc c (.mem ⟨.esp, endOffset⟩) = some endPtr := by
    have ptr := Kc.1 .esp (by decide)
    have readable : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) endOffset) 4 := by
      rw [Kc.2.1, Kc.2.2, ptr]
      exact endRead
    have raw := readSrc_mem rfl readable
    rw [Mc, ptr, endValue] at raw
    exact raw
  refine wp_cmpS read fun t T Z => WP.block_nil ?_
  have Kt : Keeps [.eax, .edx, .ecx, .ebp, .edi] s t := Kc.trans (T.keeps _)
  have ptr : c.gpr .edi = s.gpr .edi + 4 := by rw [C.gpr, Kb.1 .edi (by decide)]
  refine ⟨T.mem.trans Mc, Kt, (congrFun T.gpr .edi).trans ptr, ?_⟩
  rw [ptr] at Z
  exact Z

end VG.Proof.RsaKeyGen.X86.Trial
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure ReadControl (g : Geometry) (j : Nat) (s : State) : Prop where
  stack : StackContext g.sp s
  candidateRead : ∀ k < 2 * g.w, InRegions (s.rd ++ s.wr) (off (g.candidate.setWidth 64) (4 * k)) 4
  ending : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending
  pointer : s.gpr .edi = g.candidate + BitVec.ofNat 32 (4 * j)

theorem ReadControl.agree {g : Geometry} {j : Nat} {s t : State}
    (S : ReadControl g j s) (T : ReadControl g j t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.sp.trans T.stack.sp.symm
  · exact S.pointer.trans T.pointer.symm

theorem StateAt.readControl {g : Geometry} {c i q : Nat} {s : State}
    (S : StateAt g c i q s) (pointer : s.gpr .edi = g.candidate) : ReadControl g 0 s := by
  refine ⟨S.context.stack, S.context.candidateRead, S.ending, ?_⟩
  simpa only [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using pointer

theorem ReadControl.step_bounded {g : Geometry} (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) {j : Nat} {s : State}
    (S : ReadControl g j s) (index : j < 2 * g.w) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Trial.wordStep 4)) s fun t =>
      ReadControl g (j + 1) t ∧ t.zf = some (decide (j + 1 = 2 * g.w)) := by
  have read : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4 := by
    rw [S.pointer, Trial.word_address g.candidate (by omega) index]
    exact S.candidateRead j index
  have ending : s.mem.readW (addr (s.gpr .esp) 4) 32 = g.ending := by
    change s.mem.readW (s.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4)) 32 = _
    rw [S.stack.address 4 (by decide)]
    exact S.ending
  refine WP.mono (Trial.wordStep_control s 4 g.ending read (S.stack.access 4 (by decide)) ending)
    fun t ⟨M, K, P, Z⟩ => ?_
  have next : t.gpr .edi = g.candidate + BitVec.ofNat 32 (4 * (j + 1)) := by
    rw [P, S.pointer, BitVec.add_assoc]
    change g.candidate + (BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    congr 2 <;> omega
  refine ⟨⟨S.stack.keep K (by decide), ?_, ?_, next⟩, ?_⟩
  · intro k bound
    rw [K.2.1, K.2.2]
    exact S.candidateRead k bound
  · rw [M]; exact S.ending
  · rw [Z, S.pointer]
    have pointer : g.candidate + BitVec.ofNat 32 (4 * j) + 4 = g.candidate + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [BitVec.add_assoc]
      change g.candidate + (BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4) = _
      rw [← BitVec.ofNat_add]
      congr 2 <;> omega
    rw [pointer]
    rw [Geometry.ending, show 8 * g.w = 4 * (2 * g.w) by omega]
    rw [Trial.pointer_zf g.candidate (by omega) index]

theorem ReadControl.step {g : Geometry} (v : g.Valid) {j : Nat} {s : State}
    (S : ReadControl g j s) (index : j < 2 * g.w) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Trial.wordStep 4)) s fun t =>
      ReadControl g (j + 1) t ∧ t.zf = some (decide (j + 1 = 2 * g.w)) :=
  S.step_bounded v.widthBound v.candidateFit index

end VG.Proof.RsaKeyGen.X86.Sieve
