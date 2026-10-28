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

/-- The dispatch over `widths` runs `part w` for the width `w` in `eax`, from
a state that differs from the entry's only in its flags. -/
theorem dispatch_ok {part : Nat → Prog isa} {w : Nat} {s : State} {Q : State → Prop}
    (width : s.gpr .eax = BitVec.ofNat 32 w) (wBound : w < 2 ^ 32)
    (widths : List Nat) (member : w ∈ widths) (bounded : ∀ x ∈ widths, x < 2 ^ 32)
    (H : ∀ a, Fupd s a → WP isa (part w) a Q) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.dispatch part widths) s Q := by
  induction widths generalizing s with
  | nil => cases member
  | cons x rest ih =>
    unfold VG.Impl.RsaKeyGen.X86.Candidate.dispatch
    refine WP.seq (wp_cmpS rfl fun a A Z => WP.block_nil ?_)
    have condition : isa.eval .e a = some (decide (w = x)) := by
      change a.zf = _
      rw [Z, width]
      exact congrArg some (width_comparison wBound (bounded x List.mem_cons_self))
    by_cases same : w = x
    · refine WP.ite true (by rw [condition, decide_eq_true same]) (fun _ => ?_) (fun bad => nomatch bad)
      rw [← same]
      exact H a A
    · refine WP.ite false (by rw [condition, decide_eq_false same]) (fun bad => nomatch bad) (fun _ => ?_)
      exact ih (by rw [A.gpr]; exact width) (List.mem_cons.mp member |>.resolve_left same)
        (fun j mem => bounded j (List.mem_cons_of_mem _ mem)) (fun b B => H b (A.trans B))

end VG.Proof.RsaKeyGen.X86.Candidate
