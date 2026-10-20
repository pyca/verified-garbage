module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightColumns
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64.ProductEight
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

private theorem pending_power (i j : Nat) :
    2 ^ (64*i) * 2 ^ (64*i) * (2 ^ 64) ^ j = 2 ^ (64*(2*i+j)) := by
  rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

private theorem pending_scale {w r p c a b term : Nat}
    (hp : w*w*r = p) (hl : a+w*(w*r*c) = b+w*term+w*0) : a+p*c = b+w*term := by
  grind

/-- The first triangular row has no earlier tiles. Later rows retain the
pending carry in the existing eight-limb product invariant. -/
theorem offDiagonal_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0) (h16 : s.gpr .x16 = off B eT)
    (h17 : s.gpr .x17 = off B eN) (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64*(k+1) ≤ Z) (hN : eN+64*k ≤ Z)
    (hQT : eQ+64 ≤ eT ∨ eT+64*(k+1) ≤ eQ)
    (hNT : eN+64*k ≤ eT ∨ eT+64*(k+1) ≤ eN) (hk : k < 2 ^ 64) :
    WP isa (.ite (.nonzero .x .x15)
      (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])) s
      (ProductColumnInv s B eQ eT eN k k) := by
  by_cases hz : k = 0
  · subst k
    refine WP.ite false (by rw [eval_nonzero, h15]; rfl) (by simp) (fun _ => ?_)
    apply WP.block_nil
    refine ⟨?_, ?_, ?_, ?_, Outside.refl _ _ _ _, Keep.refl _ _⟩
    · simp only [h10, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, show wv s.mem B eN 0 = 0 from rfl]
    · rw [h10]; exact Nat.zero_le 1
    · simpa only [Nat.mul_zero, Nat.add_zero] using h16
    · simpa only [Nat.mul_zero, Nat.add_zero] using h17
  · refine WP.ite true (by
      rw [eval_nonzero, h15, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      simp [hz]) (fun _ => ?_) (by simp)
    exact productColumns_ok hs h8 h7 h10 h16 h17 h15 hQ hT hN hQT hNT (by omega) hk

/-- Lift the off-diagonal products and their pending carry to the full
square buffer, including every untouched word. -/
theorem offDiagonal_full {s : State} {B : Addr} {Z eQ eT eN i n : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0) (h16 : s.gpr .x16 = off B (eT+64*i))
    (h17 : s.gpr .x17 = off B eN) (h15 : s.gpr .x15 = BitVec.ofNat 64 i)
    (hQ : eQ+64 ≤ Z) (hT : eT+8*n ≤ Z) (hN : eN+64*i ≤ Z)
    (hQT : eQ+64 ≤ eT ∨ eT+8*n ≤ eQ)
    (hNT : eN+64*i ≤ eT ∨ eT+8*n ≤ eN) (hi : i < 2 ^ 64) (hin : 16*i+8 ≤ n) :
    WP isa (.ite (.nonzero .x .x15)
      (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])) s fun t =>
      wv t.mem B eT n + 2 ^ (64*(16*i+8))*(t.gpr .x10).toNat =
        wv s.mem B eT n + 2 ^ (64*(8*i))*(wv s.mem B eQ 8 * wv s.mem B eN (8*i)) ∧
      Outside B (eT+64*i) (64*(i+1)) s.mem t.mem ∧ Keep productColumnRegs s t := by
  have hn := hs.nowrap
  refine WP.mono (offDiagonal_ok hs h8 h7 h10 h16 h17 h15 hQ (by omega) hN
    (by omega) (by omega) hi) fun t ht => ?_
  have hf := ProductEight.wv_window_delta (n := n) (j := 8*i) (k := 8*(i+1))
    (by omega : eT+8*n ≤ 2 ^ 64) (by omega)
    (by simpa only [show 8*(8*i) = 64*i by omega, show 8*(8*(i+1)) = 64*(i+1) by omega] using ht.frame)
  simp only [show 8*(8*i) = 64*i by omega] at hf
  have hv := ht.value
  have heq : wv t.mem B (eT+64*i) (8*(i+1)) +
      (2 ^ (64*(8*i)) * (2 ^ 64) ^ 8) * (t.gpr .x10).toNat =
        wv s.mem B (eT+64*i) (8*(i+1)) + wv s.mem B eQ 8 * wv s.mem B eN (8*i) + 0 :=
    hv.trans (Nat.add_zero _).symm
  have hl := ProductEight.window_lift hf heq
  have hp : (2 ^ (64*(8*i)) * 2 ^ (64*(8*i))) * (2 ^ 64) ^ 8 = 2 ^ (64*(16*i+8)) := by
    simpa only [show 2*(8*i) = 16*i by omega] using pending_power (8*i) 8
  exact ⟨pending_scale hp hl, ht.frame, ht.keep⟩

end VG.Proof.Bignum.AArch64.SquareEight
