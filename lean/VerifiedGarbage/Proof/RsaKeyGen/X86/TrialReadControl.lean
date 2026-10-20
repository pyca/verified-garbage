module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialPointer

/-! # Only pointers and the fixed word count control a single divisor's trace -/

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

theorem ReadControl.step {g : Geometry} (v : g.Valid) {j : Nat} {s : State}
    (S : ReadControl g j s) (index : j < 2 * g.w) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Trial.wordStep 4)) s fun t =>
      ReadControl g (j + 1) t ∧ t.zf = some (decide (j + 1 = 2 * g.w)) := by
  have read : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4 := by
    rw [S.pointer, Trial.word_address g.candidate (by have := v.candidateFit; omega) index]
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
    rw [Trial.pointer_zf g.candidate (by have := v.widthBound; omega) index]

end VG.Proof.RsaKeyGen.X86.Sieve
