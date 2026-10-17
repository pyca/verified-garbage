module

public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The `_alt` ladder's 255 iterations -/

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
    (hg : Good (env s.mem base) x1 (init x1)) (hw : word s.mem base 768 = 0)
    (hb : ∀ i < 255, s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i))
    (hB : Bel s.mem base S14) :
    WP isa VG.Impl.X25519.AArch64.AltLadder.ladder s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 0) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 0).swap := by
  refine WP.seq (WP.mono (setCounter_ok s 255) fun a ⟨ac, ka⟩ => ?_)
  have kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 255 ∧ LInv base s k x1 n t)
    ?_ 255 a ⟨by decide, by decide, kla, by simpa [ka.mem, ladderAfter_255] using hg, ac,
      by rw [ka.mem, ladderAfter_255]; exact hw, fun i hi => by rw [ka.mem]; exact hB i hi⟩
  intro n t ⟨h1, h255, kt, gt, ct, wt, bt⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega⟩
  refine WP.mono (step_ok (k := k) (kt.scratch hs) (by omega) gt
    (ladderAfter_swap_le _ _ (by omega)) ct wt (by rw [kt.bit (by omega)]; exact hb i (by omega)) bt)
    fun u ⟨ku, gu, cu, wu, bu⟩ => ?_
  have klu : LoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega)] at gu
  have ws : word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega)]
    exact wu
  have he : isa.eval (.nonzero .x .x19) u = some (decide (i ≠ 0)) := by
    simp only [eval, VG.Proof.Ed25519.AArch64.read_x, cu,
      VG.Proof.Ed25519.AArch64.counter_nonzero (by omega : i < 2^64)]
  by_cases hi : i = 0
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws⟩
  · exact .inr ⟨by rw [he]; simp [hi], i, by omega, by omega, by omega, klu, gu, cu, ws, bu⟩

end VG.Proof.X25519.AArch64.AltLadder
