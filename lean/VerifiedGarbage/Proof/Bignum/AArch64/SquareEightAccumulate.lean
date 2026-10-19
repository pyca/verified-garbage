module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightStep
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

def pairSum (s : State) (ps : List (Nat × Nat)) : Nat → Nat
 | 0 => 0
 | n + 1 => pairSum s ps n + pairValue s ps n

def steps (ps : List (Nat × Nat)) (n : Nat) : List Instr :=
  (List.range n).flatMap (step ps)

theorem steps_ok {s t : State} {ps : List (Nat × Nat)} {n : Nat}
    (hps : ∀ i < ps.length, ps[i]!.1 < 8 ∧ ps[i]!.2 < 8)
    (hn : n ≤ ps.length) (hq : Queue s ps 0 t) (hk : Keep workRegs s t)
    (h7 : t.gpr .x7 = 0) (hb : accValue t + pairSum s ps n < 2 ^ 192) :
    WP isa (.block (steps ps n)) t fun u =>
      Queue s ps n u ∧ accValue u = accValue t + pairSum s ps n ∧
        u.mem = t.mem ∧ Keep workRegs t u := by
  induction n with
  | zero => exact WP.block_nil ⟨hq, by simp [pairSum], rfl, Keep.refl _ _⟩
  | succ n ih =>
    have hb' : accValue t + pairSum s ps n < 2 ^ 192 := by
      simp only [pairSum] at hb
      omega
    rw [steps, List.range_succ, List.flatMap_append]
    apply WP.block_append
    refine WP.mono (ih (by omega) hb') fun v ⟨hqv, hav, hmv, kv⟩ => ?_
    have hk' : Keep workRegs s v := (hk.trans kv).mono (by simp)
    have h7' : v.gpr .x7 = 0 := (kv.gpr _ (by decide)).trans h7
    have hb'' : accValue v + pairValue s ps n < 2 ^ 192 := by
      simp only [pairSum] at hb
      omega
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      WP.mono (step_ok hps (by omega) hqv hk' h7' hb'')
        (fun u ⟨hqu, hau, hmu, ku⟩ =>
          ⟨hqu, by simp only [pairSum]; omega, hmu.trans hmv,
            (kv.trans ku).mono (by simp)⟩)

theorem pairValue_lt (s : State) (ps : List (Nat × Nat)) (j : Nat) :
    pairValue s ps j < 2 ^ 128 := by
  have ha := (s.gpr inputs[ps[j]!.1]!).isLt
  have hb := (s.gpr inputs[ps[j]!.2]!).isLt
  have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
  simpa only [pairValue, ← Nat.pow_add] using h

theorem pairSum_le (s : State) (ps : List (Nat × Nat)) (n : Nat) :
    pairSum s ps n ≤ n * (2 ^ 128 - 1) := by
  induction n with
  | zero => simp [pairSum]
  | succ n ih =>
    have h := pairValue_lt s ps n
    rw [pairSum, Nat.succ_mul]
    omega

/-- At most four off-diagonal products fit in a column. The third carry
limb leaves ample headroom, including the incoming two-limb carry. -/
theorem column_accumulate_ok {s : State} {k : Nat}
    (hk : k < 15) (h7 : s.gpr .x7 = 0) (hb : accValue s < 2 ^ 128) :
    WP isa (.block (product (pairs k) 0 ++ product (pairs k) 1 ++
      steps (pairs k) (pairs k).length)) s fun t =>
        accValue t = accValue s + pairSum s (pairs k) (pairs k).length ∧
          t.mem = s.mem ∧ Keep workRegs s t := by
  have hps : ∀ i < (pairs k).length, (pairs k)[i]!.1 < 8 ∧ (pairs k)[i]!.2 < 8 := by
    intro i hi
    have h := pair_bounds k hk i hi
    exact ⟨by omega, h.2.1⟩
  have hs := pairSum_le s (pairs k) (pairs k).length
  have hl := pairs_length k hk
  have bound : accValue s + pairSum s (pairs k) (pairs k).length < 2 ^ 192 := by omega
  apply WP.block_append
  refine WP.mono (queue_init_ok hps) fun t ⟨hq, ha, hm, kt⟩ => ?_
  refine WP.mono (steps_ok hps (Nat.le_refl _) hq kt
    ((kt.gpr _ (by decide)).trans h7) (by omega)) fun u ⟨_, hu, hum, ku⟩ => ?_
  exact ⟨by omega, hum.trans hm, (kt.trans ku).mono (by simp)⟩

end VG.Proof.Bignum.AArch64.SquareEight
