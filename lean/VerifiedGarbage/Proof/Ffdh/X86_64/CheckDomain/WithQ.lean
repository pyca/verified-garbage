module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work

/-! # FFDH domain validation on x86-64: the optional subgroup order -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem bit_and_left {P Q : Prop} [Decidable P] [Decidable Q] (hp : P) : bit Q = bit (P ∧ Q) := by
  by_cases hq : Q <;> simp [bit, hp, hq]

abbrev CdP.relation (p : CdP) : Prop := p.qr ∧ (p.P - 1) % p.Q = 0 ∧ p.G ^ p.Q % p.P = 1

private theorem withQ_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code) =
      .block [enter] :: (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange ++
        ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ, List.cons_append, List.nil_append]

theorem withQ_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = p.B) (hm : p.mv = true) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit p.relation) := by
  rw [withQ_eq]
  refine wp_seqs_cons (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (h.enter hd) fun u ⟨hw, hdi, hm', k⟩ => ?_)
  have S₁ : StepPost p s (fun _ => True) u := ⟨trivial, by rw [hm']; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm']), k.mono (by decide)⟩
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (WP.mono (order_range hw hdi hq) fun v S₂ => ?_)
  have H := S₁.trans S₂
  obtain ⟨hw', hd', hz⟩ := S₂.1
  simp only [seqs]
  refine WP.ite (!decide p.qr) (by simp [eval, hz]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬p.qr := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hn)
    refine WP.mono (ret_inner (hw'.mem.ctx hd') (r := 0) (by decide)) fun t ⟨hdi, ha, hmem, kk⟩ => ?_
    exact ⟨⟨hdi, by simpa [bit, CdP.relation, hn'] using ha⟩, by rw [hmem]; exact H.2.1,
      (fun i hi => by rw [hmem]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (kk.mono (by decide))⟩
  · have hy' : p.qr := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hy)
    exact WP.mono (divides_ok M E R hw' hd' hm hq hy'.1 hy'.2.1) fun t S₃ =>
      ⟨⟨S₃.1.1, S₃.1.2.trans (bit_and_left hy')⟩, (H.trans S₃).2⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
