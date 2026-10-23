module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Clearing native words of a witness above a narrow candidate's width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLoad
open VG.Impl.Mont.X86 (sc)

theorem zeros_succ (o n : Nat) :
    zeros o (n + 1) = zeros o n ++ ([.mov .eax (.imm 0), .store (sc (o + 4 * n)) .eax] : List Instr) := by
  simp only [zeros, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- `n` words at `o` cleared, nothing else written. -/
theorem zeros_ok {s : State} {base : Addr} {size : Nat} (scratch : Scr s base size) (o : Nat) :
    ∀ n, o + 4 * n ≤ size → WP isa (.block (zeros o n)) s fun t =>
      val32 t.mem base o n = 0 ∧ Outside base o (4 * n) s.mem t.mem ∧ Keeps [.eax] s t
  | 0, _ => WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | n + 1, fit => by
    rw [zeros_succ]
    refine WP.block_append (WP.mono (zeros_ok scratch o n (by omega_arith)) fun a ⟨Va, Oa, Ka⟩ => ?_)
    have Sa := scratch.of_keeps Ka (by decide)
    refine wp_movS rfl fun b B _ => ?_
    have Sb := scratch.of_keeps (Ka.widen B.keeps) (by decide)
    refine wp_storeS (Sb.ea (d := o + 4 * n) (by omega_arith)) (Sb.write (d := o + 4 * n) (n := 4) (by omega_arith))
      fun t T => WP.block_nil ?_
    have Ot : Outside base (o + 4 * n) 4 a.mem t.mem := by
      rw [T.mem, B.mem]
      exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega_arith)
    refine ⟨?_, (Oa.mono (by omega_arith) (by omega_arith)).trans (Ot.mono (by omega_arith) (by omega_arith)),
      (Ka.widen B.keeps).widen (T.keeps [])⟩
    have top : w32 t.mem base (o + 4 * n) = 0 := by
      rw [T.mem]
      exact (w32_write_self _ _ _ _).trans (by rw [B.gpr]; rfl)
    rw [val32_succ, Ot.val32 (by omega_arith) (by have := scratch.nowrap; omega_arith), Va, top, Nat.mul_zero]

end VG.Proof.RsaKeyGen.X86.WitnessLoad
