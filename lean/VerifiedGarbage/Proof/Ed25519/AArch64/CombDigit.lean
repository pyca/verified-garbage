module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
public import VerifiedGarbage.Proof.Ed25519.CombDigits
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# The comb's digits and signs

Step `i` reads the nibble `i` of the scalar from its bits,
expanded one per byte at byte 768 of the workspace, by Horner's rule;
`combSign` turns it into the magnitude `|n - 8|` and the mask of its sign.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

/-! ## The bit index -/

private theorem index_fact : ∀ j < 64, BitVec.ofNat 64 j <<< 2 = BitVec.ofNat 64 (4 * j) := by
  decide +kernel

theorem combIndex_ok (s : State) {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 64)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x8 .x19 2, .add .x .x8 .x0 .x8] : List Instr)) s fun t =>
      t.gpr .x8 = off base (4 * j) ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (2 : Nat) < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, index_fact j hj, hs.x0, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
      by simp only [RegUpd.rd_write],
      by simp only [RegUpd.wr_write],
      by simp only [RegUpd.sp_write]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem combNibble_ok {s : State} {base : Addr} (hs : Scr s base) {S i p o : Nat} (hi : i < 64)
    (hp : s.gpr .x8 = off base p) (hpo : p + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block (combNibble o)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib S i) ∧ Keeps [.x2, .x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : ∀ j, off base p + BitVec.ofNat 64 (o + j) = off base (768 + (4 * i + j)) :=
    fun j => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (off base) (by omega)
  have hv : ∀ j < 4, ((s.mem (off base (768 + (4 * i + j)))).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (4 * i + j)) % 2) := fun j hj => by
    rw [hb _ (by omega)]; exact bit_ext _ (Nat.mod_lt _ (by decide))
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [combNibble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show o + 3 < 4096 * 1 by omega, show o + 2 < 4096 * 1 by omega, show o + 1 < 4096 * 1 by omega,
    show o < 4096 * 1 by omega,
    Nat.reduceMul, and_self, hp, e0, e1, e2, e3,
    r0, r1, r2, r3, read_byte, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
      by simp only [RegUpd.rd_write],
      by simp only [RegUpd.wr_write],
      by simp only [RegUpd.sp_write]⟩⟩
  · rw [nib_bits]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Sign and magnitude -/

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^
        (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) ∧
    ((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63 =
      mask (decide (n < 8)) := by
  decide +kernel

theorem combSign_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x1 = mask (decide (n < 8)) ∧
      Keeps [.x1, .x2, .x3, .x9] s t := by
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 32 from by decide, Nat.mul_zero, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, (sign_fact n hn).2, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
      by simp only [RegUpd.rd_write],
      by simp only [RegUpd.wr_write],
      by simp only [RegUpd.sp_write]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
