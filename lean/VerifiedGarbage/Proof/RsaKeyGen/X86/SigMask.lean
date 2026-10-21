module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMaskMath
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Native alignment-mask instructions compute sigma > j exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.SigMask
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.SigMask

theorem flip_mask (x : Nat) :
    cmask (decide (x < 1)) ^^^ BitVec.allOnes 32 = cmask (decide (x ≠ 0)) := by
  by_cases h : x = 0
  · subst x
    rfl
  · rw [decide_eq_false (show ¬ x < 1 by omega), decide_eq_true h]
    rfl

theorem code_ok {s : State} {base : Addr} {size marker j : Nat} (scratch : Scr s base size)
    (fit : marker + 8 ≤ size) :
    WP isa (.block (code marker j)) s fun t =>
      t.gpr .ecx = cmask (decide ((combined (word s.mem base marker) &&& constant j).toNat ≠ 0)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold code
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  have upper := readSrc_sc (scratch.of_keeps A.keeps (by decide)) (d := marker + 4) (by omega)
  rw [A.mem] at upper
  refine wp_orS upper fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  have V : c.gpr .eax = combined (word s.mem base marker) &&& constant j := by
    rw [C.gpr, B.gpr, A.gpr, VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add, combined_pair]
    rfl
  refine wp_cmpi fun d D cf _ => wp_sbb_self cf fun e E =>
    wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).trans (D.keeps _)).widen E.keeps).widen T.keeps⟩
  · rw [T.gpr, E.gpr, V]
    change cmask (decide ((combined (word s.mem base marker) &&& constant j).toNat < 1)) ^^^ _ = _
    exact flip_mask _
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

theorem code_sig {s : State} {base : Addr} {size marker j k : Nat} (scratch : Scr s base size)
    (fit : marker + 8 ≤ size) (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3)
    (value : word s.mem base marker = BitVec.twoPow 64 k) :
    WP isa (.block (code marker j)) s fun t =>
      t.gpr .ecx = cmask (decide (j < VG.Proof.RsaKeyGen.sigOf k)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  refine WP.mono (code_ok scratch fit) fun t ⟨V, M, K⟩ => ?_
  rw [value] at V
  have compare : ((combined (BitVec.twoPow 64 k) &&& constant j).toNat ≠ 0) ↔
      j < VG.Proof.RsaKeyGen.sigOf k := by
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
    · exact mask1 k index
    · exact mask2 k index
    · exact mask3 k index
  rw [decide_eq_decide.mpr compare] at V
  exact ⟨V, M, K⟩

end VG.Proof.RsaKeyGen.X86.SigMask
