module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowWord
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Exact arithmetic of native low-word updates with no carry or borrow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowWord
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowWord

theorem low_mod (m : Mem) (base : Addr) (out n : Nat) (positive : 0 < n) :
    val32 m base out n % 2 ^ 32 = w32 m base out := by
  rw [show n = n - 1 + 1 by omega, val32, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (m.readW (off base out) 32).isLt]

theorem parity (m : Mem) (base : Addr) (out n : Nat) (positive : 0 < n) :
    val32 m base out n % 2 = w32 m base out % 2 := by
  rw [← low_mod m base out n positive, Nat.mod_mod_of_dvd _ (by decide)]

theorem odd_low {m : Mem} {base : Addr} {out n : Nat} (positive : 0 < n)
    (odd : val32 m base out n % 2 = 1) : 0 < w32 m base out := by
  rw [parity m base out n positive] at odd
  omega

theorem even_low {m : Mem} {base : Addr} {out n : Nat} (positive : 0 < n)
    (even : val32 m base out n % 2 = 0) : w32 m base out + 1 < 2 ^ 32 := by
  rw [parity m base out n positive] at even
  have bound := (m.readW (off base out) 32).isLt
  change w32 m base out < 2 ^ 32 at bound
  omega

theorem increment_word {s : State} {base : Addr} {size out : Nat}
    (scratch : Scr s base size) (fit : out + 4 ≤ size) (bound : w32 s.mem base out + 1 < 2 ^ 32) :
    WP isa (.block (increment out)) s fun t =>
      w32 t.mem base out = w32 s.mem base out + 1 ∧ Outside base out 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold increment
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Sb := scratch.of_keeps K (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write fit) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, B.gpr, A.gpr, BitVec.toNat_add]
    change (w32 s.mem base out + 1) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt bound
  · rw [T.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

theorem decrement_word {s : State} {base : Addr} {size out : Nat}
    (scratch : Scr s base size) (fit : out + 4 ≤ size) (positive : 0 < w32 s.mem base out) :
    WP isa (.block (decrement out)) s fun t =>
      w32 t.mem base out + 1 = w32 s.mem base out ∧ Outside base out 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold decrement
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_subS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Sb := scratch.of_keeps K (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write fit) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, B.gpr, A.gpr,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact positive)]
    change w32 s.mem base out - 1 + 1 = _
    omega
  · rw [T.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

theorem increment_ok {s : State} {base : Addr} {size out n : Nat}
    (scratch : Scr s base size) (positive : 0 < n) (fit : out + 4 * n ≤ size)
    (bound : w32 s.mem base out + 1 < 2 ^ 32) :
    WP isa (.block (increment out)) s fun t =>
      val32 t.mem base out n = val32 s.mem base out n + 1 ∧ Outside base out 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (increment_word scratch (by omega) bound) fun t ⟨value, O, K⟩ => ?_
  refine ⟨?_, O, K⟩
  rw [show n = (n - 1) + 1 by omega, val32, val32, value,
    O.val32 (by omega) (by have := scratch.nowrap; omega)]
  omega

theorem decrement_ok {s : State} {base : Addr} {size out n : Nat}
    (scratch : Scr s base size) (positive : 0 < n) (fit : out + 4 * n ≤ size)
    (low : 0 < w32 s.mem base out) :
    WP isa (.block (decrement out)) s fun t =>
      val32 t.mem base out n + 1 = val32 s.mem base out n ∧ Outside base out 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (decrement_word scratch (by omega) low) fun t ⟨value, O, K⟩ => ?_
  refine ⟨?_, O, K⟩
  rw [show n = (n - 1) + 1 by omega, val32, val32,
    O.val32 (by omega) (by have := scratch.nowrap; omega)]
  omega

end VG.Proof.RsaKeyGen.X86.LowWord
