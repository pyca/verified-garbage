module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QSetup

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves

/-! # FFDH domain validation on x86-64: the complete subgroup check -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

theorem order_leave {p : CdP} {mi : BitVec 64} {s : State} (h : QWork p mi s) :
    WP isa (.block [leave]) s (StepPost p s (Scanned p)) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  refine WP.mono (leave_ok h.ctx) fun t ⟨hd, hm, k⟩ => ?_
  have hb := h.base.keep (by rw [hm]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hm])
  have hc := h.ctx.toMem.congr hm k.2.2
  have ho := Outer.of_mem hc hd (room_k hk h.base.hZ) (by omega) (by omega)
  exact ⟨⟨⟨hb, ho, by rw [hm]; exact h.g, by rw [hm]; exact h.q⟩,
      by rw [hm]; exact h.ep, by rw [hm]; exact h.el⟩,
    by rw [hm]; exact InScr.refl _ _ _, (fun _ _ => by rw [hm]), k.mono (by decide)⟩

theorem scanned_reset {p : CdP} {s : State} (h : Scanned p s) (hm : p.mv = true) :
    WP isa (seqs pSetup) s (StepPost p s fun t => ∃ mi, Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ word t.mem p.B (8 * sEp) = p.eqp ∧
      word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq) :=
  WP.mono (reset_p h.parent hm) fun t ⟨mi, hw, hd, hi, hh, k⟩ =>
    ⟨⟨mi, hw, hd, (hh _ (by decide) (by decide)).trans h.ep,
      (hh _ (by decide) (by decide)).trans h.el⟩, hi,
      (fun i hi => hh i (by omega) (by unfold sWs sFn; omega)), k⟩

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (pSetup ++ (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sG sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup, List.append_assoc, List.cons_append, List.nil_append]

theorem subgroup_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : QWork p mi s) (hm : p.mv = true) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit (p.G ^ p.Q % p.P = 1)) := by
  rw [subgroup_eq]
  refine wp_seqs_cons (by simp [pSetup]) (WP.mono (order_leave h) fun u₁ S₁ => ?_)
  refine wp_seqs_append (a := pSetup) (by simp [pSetup]) (by simp)
    (WP.mono (scanned_reset S₁.1 hm) fun u₂ S₂ => ?_)
  obtain ⟨mi', hw₂, hd₂, hep₂, hel₂⟩ := S₂.1
  refine wp_seqs_cons (by simp [pow])
    (WP.mono (subgroup_r2 M R hw₂ hd₂ hm hep₂ hel₂) fun u₃ S₃ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sEp sEl) (by simp [pow]) (by simp [isOne, eqArr])
    (WP.mono (subgroup_power M E S₃.1 hq) fun u₄ S₄ => ?_)
  exact WP.mono (subgroup_finish S₄.1.1 S₄.1.2) fun _ S₅ => (((S₁.trans S₂).trans S₃).trans S₄).trans S₅

end VG.Proof.Ffdh.X86_64.CheckDomain
