import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalLoop

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (diagonalValue diagonalValue_succ)

/-- The processed prefix and its carry, whether held in a register or flags. -/
structure ValueInv (s₀ : State) (B : Addr) (A eb i carry : Nat) (t : State) : Prop where
  out : Outside B A (16*i) s₀.mem t.mem
  val : wv t.mem B A (2*i) + 2 ^ (128*i) * carry =
    2 * wv s₀.mem B A (2*i) + diagonalValue s₀.mem B eb i

theorem value_step {s₀ s t : State} {B : Addr} {Z A eb w i carry carry' : Nat}
    (hs : Scr s B Z) (hi : i < w) (hA : A + 16*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (sep : eb + 8*w ≤ A ∨ A + 16*w ≤ eb)
    (h : ValueInv s₀ B A eb i carry s)
    (hv : wv t.mem B (A+16*i) 2 + 2^128*carry' =
      2*wv s.mem B (A+16*i) 2 +
        (word s.mem B (eb+8*i)).toNat * (word s.mem B (eb+8*i)).toNat + carry)
    (ho : Outside B (A+16*i) 16 s.mem t.mem) :
    ValueInv s₀ B A eb (i+1) carry' t := by
  have hn := hs.nowrap
  have rt : wv s.mem B (A+16*i) 2 = wv s₀.mem B (A+16*i) 2 := h.out.wv (by omega) (by omega)
  have rx : word s.mem B (eb+8*i) = word s₀.mem B (eb+8*i) := h.out.word (by omega) (by omega)
  have rl : wv t.mem B A (2*i) = wv s.mem B A (2*i) := ho.wv (by omega) (by omega)
  rw [rt,rx] at hv
  refine ⟨?_,?_⟩
  · exact (h.out.mono (o' := A) (n' := 16*(i+1)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := A) (n' := 16*(i+1)) (by omega) (by omega))
  · have hp := h.val
    rw [show 2*(i+1) = 2*i+2 by omega, wv_add, wv_add s₀.mem B A, rl,
      show A+8*(2*i) = A+16*i by omega, show 64*(2*i) = 128*i by omega,
      show 128*(i+1) = 128*i+128 by omega, Nat.pow_add, diagonalValue_succ]
    grind

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
