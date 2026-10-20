module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # FFDH domain validation on x86-64: load public components -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

/-- Loading a public component preserves the modulus workspace. -/
theorem load_component {p : CdP} {mi : BitVec 64} {s : State} {j : Nat} {bp : Addr} {bb : List Byte}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hj : j < 32)
    (hp : word s.mem p.B (8 * j) = bp) (hs : Src s p.B p.Z bp bb) (hl : bb.length = p.k) :
    WP isa (seqs (loadArr aXm j sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧
      wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = Spec.Rsa.os2ip bb) := by
  have hc := h.mem.ctx hd
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  refine WP.mono (primeLoad_ok hc (by omega) (Nat.le_refl _) (by omega) (show aXm < 8 by decide)
    hj (show sK < 32 by decide) hp
    (by rw [hl]; exact h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) hs
    (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hl])) fun t ⟨hc', hx, ho, k⟩ => ?_
  have hf : Frm (off p.B (inner p.w)) [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem :=
    Frm.of_outside ho (by simp)
  have hXm := slot_le (w := p.w) (show aXm < 8 by decide)
  have hXm0 := hdr_lt_slot p.w aXm (show 16 < 32 by decide)
  have hr : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨by omega, hXm⟩
  have hsep : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))],
      (r.1 + r.2 ≤ slot p.w aN ∨ slot p.w aN + 8 * (p.w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot p.w aOne ∨ slot p.w aOne + 8 * (p.w + 2) ≤ r.1) := fun r he => by
    rw [List.mem_singleton.mp he]
    exact arr_off p.w (show aXm ≠ aN by decide) (show aXm ≠ aOne by decide)
  obtain ⟨hw, hi, hh⟩ := h.child hd hf hr (fun r he => (hsep r he).1) (fun r he => (hsep r he).2) k
  exact ⟨⟨hw, hc'.rdi, hx⟩, hi, hh, k.mono (by decide)⟩

theorem load_generator {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (seqs (loadArr aXm sG sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.G) :=
  load_component h hd (by decide) h.g ((h.base.dom.drop p.k).take p.k) h.base.glen

theorem load_order {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (loadArr aXm sQ sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.Q) :=
  load_component h hd (by decide) h.q ((h.base.dom.drop (2 * p.k)).take p.k) (h.base.qlen hq)

end VG.Proof.Ffdh.X86_64.CheckDomain
