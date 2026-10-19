module

public import VerifiedGarbage.Proof.Rsa.X86_64.Div
public import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! # Reuse native long division for DSA parameter generation

Candidate reduction divides by `2*q`, which is even and therefore cannot
use Montgomery reduction. The quotient is also retained: doubling it is
the exponent needed by generator construction, avoiding another division.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Keys VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.Rsa
open VG.Proof.Dsa.Generation

theorem candidateDivision_ok {s : State} {B : Addr} {Z w x q : Nat}
    {iQ iR iD iT : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hx : wv s.mem B (slot w iQ) w = x)
    (hd : wv s.mem B (slot w iD) w = 2 * q) (hq : 0 < q) :
    WP isa (divmod iQ iR iD iT) s fun t =>
      t.gpr .rdi = B ∧ Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧
      Keep (.r9 :: .r11 :: stepRegs) s t ∧
      wv t.mem B (slot w iR) (w + 1) = x % (2 * q) ∧
      wv t.mem B (slot w iQ) w = x / (2 * q) ∧
      2 * wv t.mem B (slot w iQ) w = (x + 1 - x % (2 * q) - 1) / q := by
  refine WP.mono (divmod_ok hs hdi hW hS hw1 hw hZ hQ hR hD hT dQR dQD dQT dRD dRT dDT)
    fun t ⟨ht, hf, hk, hv⟩ => ?_
  rw [hx, hd] at hv
  obtain ⟨hr, hquot⟩ := hv (Nat.mul_pos (by decide) hq)
  exact ⟨ht, hf, hk, hr, hquot, by rw [hquot, pReduction_generatorExponent x hq]⟩

end VG.Proof.Dsa.X86_64.Generation
