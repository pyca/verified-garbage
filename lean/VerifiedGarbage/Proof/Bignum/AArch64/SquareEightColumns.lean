module
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightAccumulate

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumn
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

def columnTotal (s : State) : Nat → Nat
 | 0 => 0
 | n + 1 => columnTotal s n + 2 ^ (64 * (n + 1)) * pairSum s (pairs (n + 1)) (pairs (n + 1)).length

theorem pairSum_keep {s t : State} {ps : List (Nat × Nat)} {n : Nat}
    (hps : ∀ i < n, ps[i]!.1 < 8 ∧ ps[i]!.2 < 8) (hk : Keep workRegs s t) :
    pairSum t ps n = pairSum s ps n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := inputs_keep hk
    rw [pairSum, pairSum, ih (fun i h => hps i (by omega))]
    unfold pairValue
    rw [hi _ (hps n (by omega)).1, hi _ (hps n (by omega)).2]

theorem columnSum_keep {s t : State} {k : Nat} (hk : k < 15) (hkeep : Keep workRegs s t) :
    pairSum t (pairs k) (pairs k).length = pairSum s (pairs k) (pairs k).length := by
  apply pairSum_keep _ hkeep
  intro i hi
  have h := pair_bounds k hk i hi
  exact ⟨by omega, h.2.1⟩

def columns (n : Nat) : List Instr := (List.range n).flatMap fun k => column (k + 1)

private theorem column_compose {old digit carry total next value r : Nat}
    (h : digit + r * next = carry + value) :
    old + total * digit + (total * r) * next = old + total * carry + total * value := by
  calc
    _ = old + total * (digit + r * next) := by grind
    _ = _ := by rw [h]; grind

/-- Compose the thirteen scheduled columns. The lowest output word is zero,
as every product here is strictly off diagonal. -/
theorem columns_ok {s : State} {B : Addr} {Z e n : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (he : e + 8 * (n + 1) ≤ Z) (hn : n ≤ 13)
    (h7 : s.gpr .x7 = 0) (ha : accValue s = 0) (hz : wv s.mem B e 1 = 0) :
    WP isa (.block (columns n)) s fun t =>
      wv t.mem B e (n + 1) + 2 ^ (64 * (n + 1)) * accValue t = columnTotal s n ∧
      accValue t < 2 ^ 128 ∧ Outside B (e + 8) (8*n) s.mem t.mem ∧ Keep workRegs s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨by simp [hz, ha, columnTotal], by omega, Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [columns, List.range_succ, List.flatMap_append]
    apply WP.block_append
    refine WP.mono (ih (by omega) (by omega)) fun t ⟨htv, hta, hto, kt⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (column_ok (hs.congr kt.wr) ((kt.gpr _ (by decide)).trans h16)
      (by omega) (by omega) ((kt.gpr _ (by decide)).trans h7) hta)
      fun u ⟨huv, hua, huo, ku⟩ => ?_
    refine ⟨?_, hua, (hto.mono (by omega) (by omega)).trans
      (huo.mono (by omega) (by omega)), (kt.trans ku).mono (by simp)⟩
    have hwrap := hs.nowrap
    have hp := huo.wv (d := e) (k := n + 1) (by omega) (by omega)
    have hv := column_compose (old := wv t.mem B e (n + 1)) (total := 2 ^ (64 * (n + 1))) huv
    rw [columnSum_keep (by omega) kt] at hv
    rw [wv, hp, show 64 * (n + 1 + 1) = 64 * (n + 1) + 64 by omega,
      Nat.pow_add]
    exact hv.trans (congrArg (· + 2 ^ (64 * (n + 1)) *
      pairSum s (pairs (n + 1)) (pairs (n + 1)).length) htv)

end VG.Proof.Bignum.AArch64.SquareEight
