module
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
public import VerifiedGarbage.Proof.Dsa.X86.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86.Generation.Square

/-! # Constants and control words shared by public primality-test squarings -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure RoundReady (base : Addr) (n m size : Nat) (s : State) : Prop where
  context : Context n m base size s
  width : n ≤ 48
  room : roundStatus + 4 ≤ size
  one : wordsVal s.mem base (slot n 3) n = 1
  r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m
  minus : wordsVal s.mem base (slot n 8) n = m - 1

theorem RoundReady.unchanged {base : Addr} {n m size : Nat} {s t : State} {rs : List Reg}
    (R : RoundReady base n m size s) (mem : t.mem = s.mem) (K : Keeps rs s t)
    (di : .edi ∉ rs) (sp : .esp ∉ rs) : RoundReady base n m size t :=
  ⟨⟨R.context.scr.of_keeps K di sp, R.context.size_le, mem ▸ R.context.modulus,
    R.context.gt_one, mem ▸ R.context.inverse⟩, R.width, R.room,
    mem ▸ R.one, mem ▸ R.r2, mem ▸ R.minus⟩

theorem RoundReady.bound {base : Addr} {n m size : Nat} {s : State}
    (R : RoundReady base n m size s) {j : Nat} (hj : j < 9) : slot n j + 8 * n ≤ roundCount := by
  have := slot_bound (n := n) hj
  have := R.width
  simp only [contextBytes, slot, stride, roundCount] at *
  omega

theorem RoundReady.control {base : Addr} {n m size d : Nat} {s t : State} {rs : List Reg}
    (R : RoundReady base n m size s) (hd : d = roundCount ∨ d = roundStatus)
    (O : Outside base d 4 s.mem t.mem) (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) :
    RoundReady base n m size t := by
  have far (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ d := by
    have := R.bound hj
    rcases hd with rfl | rfl <;> simp only [roundCount, roundStatus] at * <;> omega
  have val (j : Nat) (hj : j < 9) : wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by have := far j hj; omega) (by have := far j hj; have := R.context.scr.nowrap; have := R.room; rcases hd with rfl | rfl <;> simp only [roundCount, roundStatus] at * <;> omega)
  exact ⟨R.context.outside_keep K di sp O (.inl (far 0 (by decide)))
    (by rcases hd with rfl | rfl <;> decide), R.width, R.room,
    (val 3 (by decide)).trans R.one, (val 4 (by decide)).trans R.r2, (val 8 (by decide)).trans R.minus⟩

theorem squareRanges_value {base : Addr} {n j : Nat} {s t : Mem}
    (O : Outs base (productRanges n) s t) (hj : j = 3 ∨ j = 4 ∨ j = 8)
    (fit : contextBytes n ≤ 2 ^ 64) :
    wordsVal t base (slot n j) n = wordsVal s base (slot n j) n := by
  have j9 : j < 9 := by rcases hj with rfl | rfl | rfl <;> decide
  have bound := slot_bound (n := n) j9
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp only [slot, stride] <;> omega
  · simp only [stride] at bound; omega

theorem RoundReady.square {base : Addr} {n m size : Nat} {s : State} (R : RoundReady base n m size s) :
    WP isa (ordinarySquare n) s fun t => RoundReady base n m size t ∧
      wordsVal t.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n * wordsVal s.mem base (slot n 6) n % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.mono (ordinarySquare_ok R.context R.r2) fun t ⟨C, value, O, K⟩ => ?_
  have fit : contextBytes n ≤ 2 ^ 64 := by have := R.context.size_le; have := R.context.scr.nowrap; omega
  exact ⟨⟨C, R.width, R.room,
    (squareRanges_value O (.inl rfl) fit).trans R.one,
    (squareRanges_value O (.inr (.inl rfl)) fit).trans R.r2,
    (squareRanges_value O (.inr (.inr rfl)) fit).trans R.minus⟩, value, O, K⟩
end VG.Proof.Dsa.X86.Generation
