module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab

import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import Mathlib.Data.Int.ModEq

/-! Repeated squaring for wider CRT windows, preserving the existing
workspace context, header slots, memory frame and register obligations. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `n + 1` squares multiply the encoded exponent by `2^(n + 1)`.
The conditional arithmetic claim keeps the invalid-input safety path intact. -/
theorem crtSquares_ok (M : Mont) (n : Nat) {t : State} {P : Addr} {wx : Nat}
    {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x E : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X) :
    WP isa (seqs (List.replicate (n + 1) (M.mm aY aY aY))) t fun t' =>
      CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (2 ^ (n + 1) * E) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  induction n generalizing t E with
  | zero => exact crtSq_ok M hc hw hw' hR hY hYv
  | succ n ih =>
    show WP isa (.seq (M.mm aY aY aY)
      (seqs (List.replicate (n + 1) (M.mm aY aY aY)))) t _
    refine WP.seq (WP.mono (crtSq_ok M hc hw hw' hR hY hYv)
      fun u ⟨cu, yu, vu, hu, fu, ku⟩ => ?_)
    refine WP.mono (ih cu yu vu) fun v ⟨cv, yv, vv, hv, fv, kv⟩ =>
      ⟨cv, yv, ?_, fun k hk => (hv k hk).trans (hu k hk), fu.trans fv,
        (ku.trans kv).mono (by decide)⟩
    intro hQ
    rw [vv hQ, show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 from rfl, Nat.mul_assoc]

/-- Only the workspace address and width are shared between the two runs;
the modulus, inverse and accumulated value remain secret. -/
def CrtSquarePre (p : Addr × Nat) (s : State) : Prop :=
  ∃ mi X Xc, CExpCtx s p.1 p.2 mi X Xc ∧ 2 ≤ p.2 ∧ p.2 < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.2)) X ∧ wv s.mem p.1 (slot p.2 aY) p.2 < X

theorem crtSquares_ct (M : Mont) (n : Nat) :
    RelCT isa (Two CrtSquarePre)
      (seqs (List.replicate (n + 1) (M.mm aY aY aY))) (fun _ _ => True) := by
  have one : RelCT isa (Two CrtSquarePre) (M.mm aY aY aY) (fun _ _ => True) :=
    two_map (fun p => (⟨p.1, slot p.2 8, p.2⟩ : Ws))
      (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
      (M.ct (by simp [MmUse]))
  induction n with
  | zero => exact one
  | succ n ih =>
    show RelCT isa (Two CrtSquarePre) (.seq (M.mm aY aY aY)
      (seqs (List.replicate (n + 1) (M.mm aY aY aY)))) _
    refine RelCT.seq (two_post (Ψ := CrtSquarePre) one ?_) ih
    rintro p s ⟨mi, X, Xc, hc, hw, hw', hR, hy⟩
    exact WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0)
      hc hw hw' hR hy (fun h => h.elim)) fun t ⟨ht, hyt, _⟩ =>
        ⟨mi, X, Xc, ht, hw, hw', hR, hyt⟩

end VG.Proof.Bignum.AArch64
