module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # Public width dispatch runs the code for the width in `eax` -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem _root_.VG.X86.Wp.Fupd.trans {s a b : State} (A : Fupd s a) (B : Fupd a b) : Fupd s b :=
  ⟨B.gpr.trans A.gpr, B.mem.trans A.mem, B.rd.trans A.rd, B.wr.trans A.wr, B.syms.trans A.syms⟩

theorem _root_.VG.X86.Wp.Fupd.refl (s : State) : Fupd s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem width_comparison {a b : Nat} (aBound : a < 2 ^ 32) (bBound : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0#32) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound]

end VG.Proof.RsaKeyGen.X86.Candidate
