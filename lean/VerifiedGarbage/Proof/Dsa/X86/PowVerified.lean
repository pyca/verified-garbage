module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Dsa.ModPowContract

/-! # IA-32 modular exponentiation against the shared DSA specification -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

/-- All-one bytes make the workspace modulus odd and greater than one. -/
def satState : State where
  gpr r := if r = .esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 1
  rd := [⟨0xf0000004, 8⟩]
  wr := [⟨0x01010101, 0x01010101 * 8⟩]

theorem read_ones (a : Addr) : ∀ k, (Mem.read (fun _ => 1) a (k + 2)).toNat % 2 = 1 ∧
    255 < (Mem.read (fun _ => 1) a (k + 2)).toNat := by
  intro k
  rw [read_toNat_succ, read_toNat_succ]
  rw [show (1 : BitVec 8).toNat = 1 from rfl]
  omega

theorem satisfiable {n e : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) :
    ∃ s, (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pre s := by
  refine ⟨satState, ?_⟩
  have a0 : arg satState 0 = 0x01010101 := by decide
  have a1 : arg satState 1 = 0x01010101 := by decide
  sig_pre [Proof.Dsa.ModPow.powContract, Proof.Dsa.ModPow.sig, layout, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a0, a1]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  · rw [show BitVec.toNat (16843009 : BitVec 32) = 16843009 from rfl]
    simp only [contextBytes, slot, stride]; omega
  all_goals
    obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 2 := ⟨8 * n - 2, by omega⟩
    unfold Proof.Dsa.ModPow.numAt
    rw [hk]
  · exact (read_ones _ k).1
  · exact Nat.lt_trans (by decide) (read_ones _ k).2

theorem verified (n e : Nat) (hn : 2 ≤ n := by decide) (hn48 : n ≤ 48 := by decide)
    (he : 1 < e := by decide) (hen : e ≤ 2 * n := by decide) :
    Verified target (body n e) (Proof.Dsa.ModPow.powContract (layout n e) abi 96) :=
  ⟨correct hn hn48 he hen, constantTime hn hn48 he hen, satisfiable hn hn48⟩

end VG.Proof.Dsa.X86.Pow
