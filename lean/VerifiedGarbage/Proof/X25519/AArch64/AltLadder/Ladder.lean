module

public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Word.Step

/-! # The `_alt` ladder's iterations for bits 253 down to 3 -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519 VG.Proof.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Word (LoopKeep Good Scratch bitOffset setCounter_ok)

/-- The loop's invariant. -/
def LInv (base : Addr) (s₀ : State) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop :=
  LoopKeep base s₀ s ∧ Good (env s.mem base) x1 (ladderAfter k x1 n) ∧
  s.gpr .x19 = BitVec.ofNat 64 n ∧ word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
  Bel s.mem base S14

theorem ladder_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} (hs : Scratch s base)
    (hg : Good (env s.mem base) x1 (ladderAfter k x1 254))
    (hw : word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 254).swap)
    (hb : ∀ i < 255, s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i))
    (hB : Bel s.mem base S14) :
    WP isa VG.Impl.X25519.AArch64.AltLadder.ladder s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 3) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 3).swap ∧ Bel t.mem base S14 := by
  refine WP.seq (WP.mono (setCounter_ok s 254) fun a ⟨ac, ka⟩ => ?_)
  have kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  refine WP.loop (M := isa) (fun n t => 4 ≤ n ∧ n ≤ 254 ∧ LInv base s k x1 n t)
    ?_ 254 a ⟨by decide, by decide, kla, by rw [ka.mem]; exact hg, ac,
      by rw [ka.mem]; exact hw, fun i hi => by rw [ka.mem]; exact hB i hi⟩
  intro n t ⟨h4, h254, kt, gt, ct, wt, bt⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega⟩
  refine WP.mono (step_ok (k := k) (kt.scratch hs) (by omega) (by omega) gt
    (ladderAfter_swap_le _ _ (by omega)) ct wt (by rw [kt.bit (by omega)]; exact hb i (by omega)) bt)
    fun u ⟨ku, gu, cu, du, wu, bu⟩ => ?_
  have klu : LoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega)] at gu
  have ws : word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega)]
    exact wu
  have he : isa.eval (.nonzero .x .x16) u = some (decide (i - 3 ≠ 0)) := by
    simp only [eval, VG.Proof.Ed25519.AArch64.read_x, du,
      VG.Proof.Ed25519.AArch64.counter_nonzero (by omega : i - 3 < 2^64)]
  by_cases hi : i = 3
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws, bu⟩
  · exact .inr ⟨by rw [he]; simp only [Option.some.injEq, decide_eq_true_eq]; omega,
      i, by omega, by omega, by omega, klu, gu, cu, ws, bu⟩

end VG.Proof.X25519.AArch64.AltLadder
