module

public import VerifiedGarbage.Impl.Bignum.X86.PrimeMask
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Combine the lower bound and low-bit checks as a secret mask -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Ecdsa.X86

theorem primeMaskFinish_ok {s : State} {base : Addr} {bytes n m : Nat}
    (hs : Scr s base bytes) (bound : slot n 0 + 4 ≤ bytes)
    (low : m % 2 ^ 32 = w32 s.mem base (slot n 0))
    (less : s.gpr .eax = mask32 (1 < m)) :
    WP isa (.block (primeMaskFinish n)) s fun t =>
      t.gpr .ecx = mask32 (1 < m ∧ m % 2 = 1) ∧ t.mem = s.mem ∧ Keeps [.ecx, .edx] s t := by
  unfold primeMaskFinish
  refine wp_movS (readSrc_sc hs bound) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  refine wp_movS rfl fun w W _ => ?_
  refine wp_subS rfl fun x X _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have eax : x.gpr .eax = s.gpr .eax := by
    rw [X.other _ (by decide), W.other _ (by decide), V.other _ (by decide), U.other _ (by decide)]
  have bit : v.gpr .edx = BitVec.ofNat 32 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [V.gpr, U.gpr, ite_eq_left rfl, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat]
    change m % 2 ^ 32 = (s.mem.readW (off base (slot n 0)) 32).toNat at low
    omega
  refine ⟨?_, T.mem.trans (X.mem.trans (W.mem.trans (V.mem.trans U.mem))),
    ((((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))).widen W.keeps).widen X.keeps).widen T.keeps⟩
  rw [T.gpr, X.gpr, W.gpr, W.other _ (by decide), bit, eax, less, ite_eq_left rfl]
  by_cases odd : m % 2 = 1
  · rw [odd]
    simp only [mask32, and_true]
    change BitVec.allOnes 32 &&& (if 1 < m then BitVec.allOnes 32 else 0) = _
    exact BitVec.allOnes_and
  · have even : m % 2 = 0 := by omega
    rw [even]
    simp only [mask32, show ¬ (0 : Nat) = 1 by decide, and_false, ite_false]
    change (0 : BitVec 32) &&& (if 1 < m then BitVec.allOnes 32 else 0) = 0
    exact BitVec.zero_and

end VG.Proof.Bignum.X86
