module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves

/-! # FFDH private-key validation on x86-64: complete scalar range check -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

theorem scalar_ok {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) (ho : p.P % 2 = 1) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s
      (StepPost p s fun t => Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
        t.gpr .rax = bit (p.sv = true)) := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange
  refine wp_seqs_append (a := isNonzero aXm) (by simp [isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (nonzero_ok h hd) fun u₁ ⟨ha₁, hm₁, k₁⟩ => ?_)
  have hw₁ := h.keep hm₁ k₁
  have hd₁ := (k₁.gpr (show .rdi ∉ mmRegs by decide)).trans hd
  have S₁ : StepPost p s (fun _ => True) u₁ := ⟨trivial, by rw [hm₁]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm₁]), k₁.mono (by decide)⟩
  simp only [seqs]
  refine WP.seq (WP.mono (storeF_ok hw₁ hd₁) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  have hF₂ : word u₂.mem (off p.B (inner p.w)) (8 * sF) = bit (0 < Spec.Rsa.os2ip xb) :=
    S₂.1.2.2.1.trans ha₁
  have hb₂ := hw₂.base
  have hk := hb₂.k1
  have hk' := hb₂.k2
  have hdl := hb₂.dl
  refine WP.seq (WP.mono (leaveQ_ok (hw₂.mem.ctx hd₂)
    (hb₂.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [KpP.headers]))
    (hb₂.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]))
    (by rcases hdl with h | h <;> omega) (by rcases hdl with h | h <;> omega))
    fun u₃ ⟨hd₃, _, hz₃, hm₃, k₃⟩ => ?_)
  have hw₃ := hw₂.keep hm₃ k₃
  have hF₃ : word u₃.mem (off p.B (inner p.w)) (8 * sF) = bit (0 < Spec.Rsa.os2ip xb) := by
    rw [hm₃]; exact hF₂
  have S₃ : StepPost p u₂ (fun _ => True) u₃ := ⟨trivial, by rw [hm₃]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm₃]), k₃.mono (by decide)⟩
  refine WP.seq (WP.mono (bound_ok hw₃ hd₃ hz₃ ho) fun u₄ S₄ => ?_)
  have hw₄ := S₄.1.1
  have hd₄ := S₄.1.2.1
  have hF₄ : word u₄.mem (off p.B (inner p.w)) (8 * sF) = bit (0 < Spec.Rsa.os2ip xb) :=
    S₄.1.2.2.2.trans hF₃
  refine WP.mono (andF_flag hw₄ hd₄ S₄.1.2.2.1 hF₄) fun t S₅ => ?_
  have H := (((S₁.trans S₂).trans S₃).trans S₄).trans S₅
  have he : (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < p.upper) ↔ p.sv = true := by
    rw [← h.base.valid]
    simp only [Spec.Ffdh.privateValid, Bool.and_eq_true, decide_eq_true_eq]
    rfl
  refine ⟨⟨S₅.1.1, S₅.1.2.1, ?_⟩, H.2⟩
  simpa only [bit, he] using S₅.1.2.2

end VG.Proof.Ffdh.X86_64.CheckPrivate
