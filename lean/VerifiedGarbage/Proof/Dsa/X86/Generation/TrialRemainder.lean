module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
import VerifiedGarbage.Proof.Mont.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.SmallRemainder
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The reciprocal reducer computes a canonical small-prime remainder -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem smallRemainder_ok {s : State} {x p : Nat} (hp : 1 < p) (pfit : p < 65536) (xfit : x < 2 ^ 32)
    (xb : s.gpr .ebx = BitVec.ofNat 32 x) (ps : s.gpr .esi = BitVec.ofNat 32 p)
    (vi : s.gpr .edi = BitVec.ofNat 32 (2 ^ 32 / p)) :
    WP isa (.block smallRemainder) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (x % p) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  let q := x * (2 ^ 32 / p) / 2 ^ 32
  let r := x - q * p
  have vfit : 2 ^ 32 / p < 2 ^ 32 := Nat.div_lt_self (by decide) hp
  have qr := reciprocal_remainder (by decide : 0 < 2 ^ 32) (by omega : 0 < p) xfit
  change q * p ≤ x ∧ r < 2 * p at qr
  have qfit : q < 2 ^ 32 := by
    have le := Nat.le_mul_of_pos_right q (by omega : 0 < p)
    omega
  have rfit : r < 2 ^ 32 := by omega
  have qpfit : q * p < 2 ^ 32 := by omega
  unfold smallRemainder
  refine wp_movS rfl fun a sa _ => wp_mul fun b ab => wp_movS rfl fun c bc _ => wp_mul fun d cd => ?_
  have ka : Keeps [.eax, .edx] s a := sa.keeps.mono (by decide)
  have kb := ka.trans (ab.keeps.mono (by decide))
  have kc := kb.trans (bc.keeps.mono (by decide))
  have kd := kc.trans (cd.keeps.mono (by decide))
  have bq : b.gpr .edx = BitVec.ofNat 32 q := by
    rw [ab.edx, sa.gpr, xb, sa.other _ (by decide), vi]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt xfit, Nat.mod_eq_of_lt vfit]
    rfl
  have dp : d.gpr .eax = BitVec.ofNat 32 (q * p) := by
    rw [cd.eax, bc.gpr, bq, kc.1 _ (by decide), ps]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt (by omega : p < 2 ^ 32)]
  refine wp_subS rfl fun e de _ => wp_subS rfl fun f ef cf => wp_sbbS rfl cf fun g fg _ =>
    wp_logicS (.inl rfl) rfl fun h gh => wp_addS rfl fun t ht _ => WP.block_nil ?_
  have ke : Keeps [.eax, .ebx, .edx] s e := (kd.mono (by decide)).trans (de.keeps.mono (by decide))
  have kf := ke.trans (ef.keeps.mono (by decide))
  have kg := kf.trans (fg.keeps.mono (by decide))
  have kh := kg.trans (gh.keeps.mono (by decide))
  have kt := kh.trans (ht.keeps.mono (by decide))
  have er : e.gpr .ebx = BitVec.ofNat 32 r := by
    rw [de.gpr, kd.1 _ (by decide), xb, dp, BitVec.ofNat_sub_ofNat_of_le _ _ qpfit qr.1]
  have test : decide ((e.gpr .ebx).toNat < (e.gpr .esi).toNat) = decide (r < p) := by
    rw [er, ke.1 _ (by decide), ps]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt rfit, Nat.mod_eq_of_lt (by omega : p < 2 ^ 32)]
  have mask : g.gpr .eax = if r < p then BitVec.allOnes 32 else 0 := by
    rw [fg.gpr, borrow_mask, test]
    simp only [decide_eq_true_eq]
  have correction : h.gpr .eax = if r < p then BitVec.ofNat 32 p else 0 := by
    rw [gh.gpr, mask, kg.1 _ (by decide), ps]
    simp only [ite_true]
    by_cases hr : r < p <;> simp only [hr, ite_true, ite_false, BitVec.allOnes_and,
      show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_and]
  have value : t.gpr .ebx = BitVec.ofNat 32 (if r < p then r else r - p) := by
    rw [ht.gpr, gh.other _ (by decide), fg.other _ (by decide), ef.gpr, er, ke.1 _ (by decide), ps, correction]
    split
    · rw [BitVec.sub_add_cancel]
    · rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.add_zero,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  refine ⟨?_, ?_, kt⟩
  · rw [value, reciprocal_mod (by decide : 0 < 2 ^ 32) (by omega : 0 < p) xfit]
  · rw [ht.mem, gh.mem, fg.mem, ef.mem, de.mem, cd.mem, bc.mem, ab.mem, sa.mem]
end VG.Proof.Dsa.X86.Generation
