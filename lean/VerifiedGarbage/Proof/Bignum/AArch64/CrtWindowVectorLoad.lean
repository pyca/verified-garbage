module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWord
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Mathlib.Tactic.ToAdditive

/-! Four independent load/BIT pairs, sharing one row-comparison mask. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

def acc (i : Nat) : VReg := accs[i]!
def loadBits (n : Nat) : List Instr := (List.range n).flatMap fun i =>
  [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit (acc i) .v21 .v20)]
def written : List VReg := [.v21, .v16, .v17, .v18, .v19]

theorem acc_facts : ∀ i < 4, acc i ≠ .v20 ∧ acc i ≠ .v21 ∧ acc i ∈ written := by decide

theorem acc_ne : ∀ i < 4, ∀ j < 4, i ≠ j → acc i ≠ acc j := by decide

theorem loadBits_ok (n : Nat) {s : State} {choose : Prop} [Decidable choose]
    (hn : n ≤ 4) (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hld : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (loadBits n)) s fun t =>
      (∀ i < 4, t.v (acc i) = if i < n ∧ choose then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      VKeep written s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => by simp, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    rw [show loadBits (n + 1) = loadBits n ++
      [.ldrq .v21 .x16 (16 * n), .vop (.bsel .bit (acc n) .v21 .v20)] by
        simp [loadBits, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega) (fun i hi => hld i (by omega))) fun t ⟨hv, kt⟩ => ?_
    refine WP.mono (loadBit_value (choose := choose) (acc_facts n (by omega)).2.1 (by omega)
      (by rw [kt.v .v20 (by decide)]; exact hm)
      (by rw [kt.rd, kt.wr, kt.gpr]; exact hld n (by omega))) fun u ⟨hu, ku⟩ => ?_
    refine ⟨?_, (kt.trans ku).mono ?_⟩
    · intro i hi
      by_cases he : i = n
      · subst i
        rw [hu, kt.mem, kt.gpr, hv n (by omega)]
        simp only [Nat.lt_irrefl, false_and, ite_false, Nat.lt_succ_self, true_and]
      · rw [ku.v (acc i) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨(acc_facts i hi).2.1, acc_ne i hi n (by omega) he⟩), hv i hi]
        have heq : i < n + 1 ↔ i < n := by omega
        simp only [heq]
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with hr | rfl | rfl
      · exact hr
      · decide
      · exact (acc_facts n (by omega)).2.2

end VG.Proof.Bignum.AArch64.WindowVector
