module
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Low-word parity checks before Montgomery initialization -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem word_low_bit (x : BitVec 32) : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 32 by omega)]

theorem word_odd_mask (x : BitVec 32) : 0 - (x &&& 1) = mask32 (x.toNat % 2 = 1) := by
  rw [word_low_bit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem modulus_odd_mask (p q : BitVec 32) :
    0 - (p &&& q &&& 1) = mask32 (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1) := by
  rw [word_odd_mask, BitVec.toNat_and]
  simp only [mask32, Nat.and_mod_two_eq_one]

theorem shapeParity_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hz : contextBytes n ≤ size) :
    WP isa (.block (Shape.parity n)) s fun t =>
      shapeWord t base 56 = mask32 (w32 s.mem base (slot n 0) % 2 = 1 ∧ (shapeWord s base 56).toNat % 2 = 1) ∧
      Keeps [.eax, .edx] s t ∧ Outside base 56 4 s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b0
  unfold Shape.parity
  refine wp_movS (readSrc_sc hs (d := slot n 0) (by omega_arith)) fun s1 u1 _ => ?_
  have hs1 := hs.of_keeps u1.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs1 (d := 56) (by omega_arith)) fun s2 u2 => ?_
  refine wp_logicS (.inl rfl) rfl fun s3 u3 => ?_
  refine wp_movS rfl fun s4 u4 _ => ?_
  refine wp_subS rfl fun s5 u5 _ => ?_
  have K : Keeps [.eax, .edx] s s5 := ((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps
  have hs5 := hs.of_keeps K (by decide)
  refine wp_storeS (hs5.ea (d := 56) (by omega_arith)) (hs5.write (d := 56) (n := 4) (by omega_arith)) fun t mt =>
    WP.block_nil ⟨?_, K.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, u5.gpr, u4.gpr,
      u4.other .edx (by decide), u3.gpr, u2.gpr, u1.gpr, u1.mem]
    simp only [ite_true]
    exact modulus_odd_mask _ _
  · rw [mt.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86
