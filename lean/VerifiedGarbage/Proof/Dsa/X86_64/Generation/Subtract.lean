module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! ### `Dsa.X86_64.Generation.Division`, which the modules that import this one used -/

section

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

end

end

/-! # Subtracting the p-candidate remainder without underflow -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem subtractRemainder_ok {s : State} {B : Addr} {Z w dst x rem : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : x < 16) (hr : rem < 16)
    (hdx : dst ≠ x) (hdr : dst ≠ rem)
    (hle : wv s.mem B (slot w rem) w ≤ wv s.mem B (slot w x) w) :
    WP isa (Impl.Dsa.X86_64.Generation.subtractRemainder dst x rem) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w x) w - wv s.mem B (slot w rem) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep [.r12, .r9, .rbp, .r8, .r10, .rsi, .rax, .r14] s t := by
  have sd := h.sl hd
  have sx := h.sl hx
  have sr := h.sl hr
  unfold Impl.Dsa.X86_64.Generation.subtractRemainder
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, hm, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp]
      (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₁.mem)
      (by xrun) rfl) fun s₂ ⟨⟨hbp, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base3_ok x rem dst (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
      ((k₂.gpr (by decide)).trans h9) (by decide) (by decide))
      fun s₃ ⟨h8, h10, hsi, hm₃, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (sub_ok (h.scr.congr k.2.2) h8 h10 hsi
      (((k₂.trans k₃).gpr (by decide)).trans h12)
      ((k₃.gpr (by decide)).trans hbp) (by have := h.w1; omega_using [this])
      (by have := h.w2; omega_using [this]) (by omega_using [sx]) (by omega_using [sr]) (by omega_using [sd])
      (by have := slot_sep (w := w) hdx; omega_using [this])
      (by have := slot_sep (w := w) hdr; omega_using [this])) fun t ⟨c, _, hv, ho, kt⟩ => ?_
  rw [hm₃, hm₂, hm] at hv ho
  have ht := wv_lt t.mem B (slot w dst) w
  have hn := wv_lt s.mem B (slot w rem) w
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero] at hv <;> omega_arith

end VG.Proof.Dsa.X86_64.Generation
