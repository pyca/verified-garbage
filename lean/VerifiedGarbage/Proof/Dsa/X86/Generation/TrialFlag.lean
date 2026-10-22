module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The two possible zero residues become one branchless flag. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trial_flag (s : State) :
    WP isa (.block trialFlag) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .edi = 0 ∨ s.gpr .edi = s.gpr .ebx)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold trialFlag
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun u U _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.Rsa.X86.PrivChecked.zeroTest_ok u) ?_)
  rintro v ⟨first, mem, K⟩
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ =>
    wp_logicS (Or.inr rfl) rfl fun c C => ?_
  have first' : a.gpr .edx = BitVec.ofNat 32 (decide (s.gpr .edi = 0)).toNat := by
    rw [A.gpr, first, U.gpr]
  have secondInput : c.gpr .ebp = s.gpr .edi ^^^ s.gpr .ebx := by
    rw [C.gpr, B.gpr, A.other .edi (by decide), K.1 .edi (by decide), U.other .edi (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide), K.1 .ebx (by decide), U.other .ebx (by decide)]
    rfl
  refine WP.block_append (WP.mono (VG.Proof.Rsa.X86.PrivChecked.zeroTest_ok c) ?_)
  rintro d ⟨second, mem', K'⟩
  refine wp_orS rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [T.gpr, second, secondInput, K'.1 .edx (by decide), C.other .edx (by decide),
      B.other .edx (by decide), first']
    have eq : (s.gpr .edi ^^^ s.gpr .ebx = 0) ↔ s.gpr .edi = s.gpr .ebx := by
      change (s.gpr .edi ^^^ s.gpr .ebx = 0#32) ↔ _
      exact BitVec.xor_eq_zero_iff
    simp only [eq]
    have orbit (a b : Bool) : BitVec.ofNat 32 a.toNat ||| BitVec.ofNat 32 b.toNat =
        BitVec.ofNat 32 (b || a).toNat := by cases a <;> cases b <;> rfl
    rw [orbit]
    congr 1
  · rw [T.mem, mem', C.mem, B.mem, A.mem, mem, U.mem]
  · exact ((((((U.keeps.mono (by decide)).trans (K.mono (by decide))).trans
      (A.keeps.mono (by decide))).trans (B.keeps.mono (by decide))).trans
      (C.keeps.mono (by decide))).trans (K'.mono (by decide))).trans (T.keeps.mono (by decide))

end VG.Proof.Dsa.X86.Generation
