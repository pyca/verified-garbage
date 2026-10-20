module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! # Adding one to the even reduced candidate touches only its low word -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86.Dynamic

theorem incrementEven_ok {s : State} {base : Addr} {size n dst : Nat} (S : Scr s base size)
    (positive : 0 < n) (room : dst + 4 * n ≤ size) (even : val32 s.mem base dst n % 2 = 0) :
    WP isa (.block (incrementEven dst)) s fun t =>
      val32 t.mem base dst n = val32 s.mem base dst n + 1 ∧
      Outside base dst 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  have parity := val32_parity s.mem base dst (n - 1)
  rw [show n - 1 + 1 = n by omega, even] at parity
  have lowBound : w32 s.mem base dst + 1 < 2 ^ 32 := by
    have h : w32 s.mem base dst < 2 ^ 32 := (s.mem.readW (off base dst) 32).isLt
    omega
  unfold incrementEven
  refine wp_movS (readSrc_sc S (d := dst) (by omega)) fun a sa _ => wp_addi fun b ab => ?_
  have K := sa.keeps.trans ab.keeps
  have Sb := S.of_keeps K (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (d := dst) (by omega)) fun t bt => WP.block_nil ?_
  have O : Outside base dst 4 s.mem t.mem := by
    rw [bt.mem, ab.mem, sa.mem]
    exact writeW32_outside _ _ _ (by have := S.nowrap; omega)
  refine ⟨?_, O, K.trans (bt.keeps _)⟩
  have tail : val32 t.mem base (dst + 4) (n - 1) = val32 s.mem base (dst + 4) (n - 1) :=
    O.val32 (by omega) (by have := S.nowrap; omega)
  have low : w32 t.mem base dst = w32 s.mem base dst + 1 := by
    unfold w32
    rw [bt.mem, Mem.readW_writeW_self32, ab.gpr, sa.gpr, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt lowBound
  rw [show n = 1 + (n - 1) by omega, val32_append, val32_append]
  simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    show 32 * 1 = 32 by rfl, low, tail]
  omega
end VG.Proof.Dsa.X86.Generation
