module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push

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
      ((k₃.gpr (by decide)).trans hbp) (by have := h.w1; omega)
      (by have := h.w2; omega) (by omega) (by omega) (by omega)
      (by have := slot_sep (w := w) hdx; omega)
      (by have := slot_sep (w := w) hdr; omega)) fun t ⟨c, _, hv, ho, kt⟩ => ?_
  rw [hm₃, hm₂, hm] at hv ho
  have ht := wv_lt t.mem B (slot w dst) w
  have hn := wv_lt s.mem B (slot w rem) w
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.X86_64.Generation
