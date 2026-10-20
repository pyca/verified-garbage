module

public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Row

/-! # Bounded modular doublings, including termination -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

structure DoubleInv (M : Mod) (base : Addr) (size m acc out steps i : Nat) (s t : State) : Prop where
  counter : t.gpr .esi = BitVec.ofNat 32 (steps - i)
  modulus : Modulus M size m t.mem base
  lt : wordsVal t.mem base out M.n < m
  value : wordsVal t.mem base out M.n = 2 ^ i * wordsVal s.mem base out M.n % m
  mem : Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem
  keeps : Keeps powerClob s t

theorem double_residue (i v m : Nat) :
    2 * (2 ^ i * v % m) % m = 2 ^ (i + 1) * v % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  ac_rfl

/-- A positive public number of doublings terminates and computes the
corresponding power of two times the original residue. -/
theorem doubleLoop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} {m acc out steps : Nat} (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (ho : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (hv : wordsVal s.mem base out M.n < m)
    (hk : 0 < steps) (hk32 : steps < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 steps) :
    WP isa (VG.Impl.Mont.X86.Dynamic.doubleLoop M acc out) s
      (DoubleInv M base size m acc out steps steps s) := by
  unfold VG.Impl.Mont.X86.Dynamic.doubleLoop
  have init : DoubleInv M base size m acc out steps 0 s s := by
    refine ⟨?_, hm, hv, ?_, Outs.refl _ _ _, Keeps.refl _ _⟩
    · simpa only [Nat.sub_zero] using hc
    · rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv]
  refine WP.loop (M := isa)
    (fun n t => ∃ i, n = steps - i ∧ i < steps ∧ DoubleInv M base size m acc out steps i s t)
    ?_ steps s ⟨0, rfl, hk, init⟩
  rintro n t ⟨i, rfl, hi, I⟩
  have ht := hs.of_keeps I.keeps (by decide)
  refine WP.mono (doubleStep_ok ht I.modulus hl ho I.lt (by omega) (by omega) I.counter)
    fun u ⟨count, zf, val, modU, memU, keepU⟩ => ?_
  have next : DoubleInv M base size m acc out steps (i + 1) s u := by
    refine ⟨?_, modU, ?_, ?_, I.mem.trans memU, I.keeps.trans keepU⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega]
    · rw [val]; exact Nat.mod_lt _ (by omega)
    · rw [val, I.value, double_residue]
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, hdone ▸ next⟩
    have eq : steps - i = 1 := by omega
    simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, steps - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    have ne : steps - i ≠ 1 := by omega
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

end VG.Proof.Mont.X86.Dynamic
