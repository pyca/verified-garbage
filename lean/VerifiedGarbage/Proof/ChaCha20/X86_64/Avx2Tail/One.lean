module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
public import VerifiedGarbage.Impl.ChaCha20.X86_64.BlockVL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Sym
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Out

/-!
# ChaCha20 on x86-64 with AVX-512VL: one block in `ymm` registers

`BlockVL.code`'s parts: `BlockVL.setup` broadcasts the rows of the state at
`rdi` to both lanes of the first set (`HB 1`, both lanes the state), the
rounds with `vprold` need no masks (`roundsOne_ok`), and `BlockVL.finish`
adds the state again and writes both lanes' blocks to `buf[0, 128)`, as
`last1`'s code around the rounds does without the lane increments.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word stateAt serialize innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_zreg stateAt_get)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out blk dr1_words)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)

/-! ## The kernel's checks -/

def setupOneCheck : Bool :=
  match run 0 Sym.init Impl.ChaCha20.X86_64.BlockVL.setup with
  | some σ => !σ.dirty && (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg r p == .mem 0 (4 * r + p % 4)
  | none => false

def finishOneCheck : Bool :=
  match run 0 Sym.init Impl.ChaCha20.X86_64.BlockVL.finish with
  | some σ => (List.range 2).all fun l => (List.range 16).all fun i =>
      σ.mem 1 (16 * l + i) == .add (.reg (i / 4) (4 * l + i % 4)) (.mem 0 i)
  | none => false

theorem setupOneCheck_eq : setupOneCheck = true := by decide +kernel
theorem finishOneCheck_eq : finishOneCheck = true := by decide +kernel

/-! ## The parts -/

/-- Block `l` of the set: the rounds' words `vs l` plus the input state. -/
abbrev plusOne (vs : Nat → CState) (S : CState) (l : Nat) : CState := Vector.zipWith (· + ·) (vs l) S

theorem outOne_eval {D : Nat} {s : State} {vs : Nat → CState} (hz : HB 1 vs s) {i l : Nat} (hi16 : i < 16)
    (hl : l < 2) :
    T.eval D s (.add (.reg (i / 4) (4 * l + i % 4)) (.mem 0 i)) = (plusOne vs (S0 s) l)[i] := by
  simp only [plusOne, Vector.getElem_zipWith, T.eval, yw, show (4 * l + i % 4) / 4 = l by omega,
    show (4 * l + i % 4) % 4 = i % 4 by omega, regn, baseR, stateAt_get _ _ hi16]
  have := hz 0 (by decide) l hl i hi16
  simp only [Nat.mul_zero, Nat.zero_add] at this
  rw [this]

theorem setupOne_ok {s : State} (hc : Ctx 0 s) :
    WP isa (.block Impl.ChaCha20.X86_64.BlockVL.setup) s fun s' =>
      HB 1 (fun _ => S0 s) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setupOneCheck_eq
  unfold setupOneCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega] at r
    rw [r]
    simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
  · cases e

/-- A double round with `vprold` on one set, which needs no masks. -/
theorem doubleRoundOne_ok {vs : Nat → CState} {s : State} (h : HB 1 vs s) :
    WP isa (.block doubleRound1V) s fun s' => HB 1 (fun j => innerBlock (vs j)) s' ∧ Frame' s s' := by
  rw [doubleRound1V_eq]
  refine WP.mono (blockV_ok (B := 8) _ (by decide) (hy_wordsOf s)) fun s' ⟨h', _, f⟩ =>
    ⟨hb_of h' (fun k hk l hl => ?_) (by decide), f⟩
  obtain rfl : k = 0 := by omega
  rw [dr1_words, blk_wordsOf h hk hl]

theorem roundsOne_ok {vs : Nat → CState} {s₀ : State} (h : HB 1 vs s₀) :
    ∀ n, WP isa (roundsS true 1 n) s₀ fun s =>
      HB 1 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (roundsOne_ok h n) fun _ ⟨h₁, f₁⟩ =>
      WP.mono (doubleRoundOne_ok h₁) fun _ ⟨h₂, f₂⟩ => ⟨h₂, f₁.trans f₂⟩)

theorem finishOne_ok {s : State} (hc : Ctx 0 s) {vs : Nat → CState} (hz : HB 1 vs s) :
    WP isa (.block Impl.ChaCha20.X86_64.BlockVL.finish) s fun s' =>
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plusOne vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishOneCheck_eq
  unfold finishOneCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out (f := fun l => plusOne vs (S0 s) l) ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outOne_eval hz (by omega) (by omega)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
    exact d
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx2Tail
