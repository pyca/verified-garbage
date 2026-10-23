module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Out
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-!
# FFDH on AArch64: an imported scalar's range, in constant time

Runs whose data have the same public part (`FD.pub`: all but the other
inputs' octets) leak the same through `CheckPrivate.scalarRange`
(`scalarRange_ct`), whatever the number tested: its comparisons run over
all the words, and its one branch is on the domain's length.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)

/-- A run's data without the octets of its other inputs: what two runs share. -/
abbrev FD.pub (D : FD) : FD := D.withSrcs []

/-- A stage of some run's data with the public part `a`, and some value. -/
def On (S : FD → Nat → State → Prop) (a : FD) (t : State) : Prop := ∃ D X, D.pub = a ∧ S D X t

theorem on_post {S T : FD → Nat → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (On S)) c fun _ _ => True)
    (hw : ∀ D X t, S D X t → WP isa c t fun u => T D X u ∧ KX t u) : RelCT isa (Two (On S)) c (Two (On T)) :=
  two_post hct fun _ _ ⟨D, X, hD, h⟩ => WP.mono (hw D X _ h) fun _ h => ⟨D, X, hD, h.1⟩

theorem on_post' {S T : FD → Nat → State → Prop} {c : Prog isa} {P : FD → State → Prop}
    (hct : RelCT isa (Two fun a s => On S a s ∧ P a s) c fun _ _ => True)
    (hw : ∀ D X t, S D X t → P D.pub t → WP isa c t fun u => T D X u ∧ KX t u) :
    RelCT isa (Two fun a s => On S a s ∧ P a s) c (Two (On T)) :=
  two_post hct fun _ _ ⟨⟨D, X, hD, h⟩, hp⟩ => WP.mono (hw D X _ h (by rw [hD]; exact hp)) fun _ h => ⟨D, X, hD, h.1⟩

theorem pub_eq {D₁ D₂ : FD} {a : FD} (h₁ : D₁.pub = a) (h₂ : D₂.pub = a) :
    D₁.pub = D₂.pub := h₁.trans h₂.symm

namespace ScalarRange

/-- `CheckPrivate.scalarRange`. -/
theorem scalarRange_ct : RelCT isa (Two (On S2)) (seqs CheckPrivate.scalarRange) (Two (On S7)) := by
  rw [scalarRange_eq]
  refine RelCT.seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (RelCT.seq (R := Two (On S3))
    (on_post (two_map FD.ws (fun a s ⟨D, X, hD, mi, hI, _⟩ => by subst hD; exact hI.goodW1.1)
      (geArr_ct (by decide) (by decide) (by taint_decide))) fun _ _ _ h => s2_s3 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S4)) (on_post (two_taint [.x0]
    (pins_x0B FD.G fun a s h => by obtain ⟨D, X, hD, mi, hI, _⟩ := h; subst hD; exact hI.2.1.x0)
      (by taint_decide)) fun _ _ _ h => s3_s4 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S5)) (on_post (two_taint [.x0]
    (pins_x0B FD.B fun a s h => by obtain ⟨D, X, hD, mi, hP, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2)
      (by taint_decide)) fun _ _ _ h => s4_s5 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S6)) (two_ite
    (fun a s₁ s₂ ⟨D₁, _, h₁, H₁⟩ ⟨D₂, _, h₂, H₂⟩ => by
      have e := pub_eq h₁ h₂
      have edl : D₁.dl = D₂.dl := by have := congrArg FD.dl e; exact this
      have ek : D₁.k = D₂.k := by have := congrArg FD.k e; exact this
      rw [s5_eval H₁, s5_eval H₂, edl, ek]) ?_ ?_) ?_)
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [ltP, Crt.copyArr]) (RelCT.seq
      (R := Two (On fun D X t => S5e D X t ∧ D.dl = 2 * D.k)) (on_post' (two_taint [.x0]
        (pins_x0B FD.B fun a s (h : On S5 a s ∧ _) => by
          obtain ⟨⟨D, X, hD, mi, hP, _⟩, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun D X s h he => WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.choose_spec.1.1.noq (Option.some.inj ((s5_eval h).symm.trans he))⟩, k⟩) ?_)
    exact on_post (two_map FD.ws (fun a s ⟨D, X, hD, ⟨mi, hI, _⟩, _⟩ => by subst hD; exact hI.goodW1)
      (ltP_ct (by decide) (by decide) (by taint_decide) (by taint_decide))) fun _ _ _ h => e_s6n h.1 h.2
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq
      (R := Two (On fun D X t => S5e D X t ∧ D.dl = 3 * D.k)) (on_post' (two_taint [.x0]
        (pins_x0B FD.B fun a s (h : On S5 a s ∧ _) => by
          obtain ⟨⟨D, X, hD, mi, hP, _⟩, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun D X s h he => WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.choose_spec.1.1.q (Option.some.inj ((s5_eval h).symm.trans he))⟩, k⟩) ?_)
    refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two (On S5q))
      (on_post (two_map (fun a : FD => a.ld (a.dp + BitVec.ofNat 64 (2 * a.k)) a.k)
          (fun a s ⟨D, X, hD, h⟩ => by subst hD; exact (e_lpreQ h.1 h.2 :))
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun _ _ _ h => e_q h.1 h.2) ?_)
    exact on_post (two_map FD.ws (fun a s ⟨D, X, hD, ⟨mi, hI, _⟩, _⟩ => by subst hD; exact hI.goodW1.1)
      (ltArr_ct (by decide) (by decide) (by taint_decide))) fun _ _ _ h => q_s6 h
  rw [seqs_one]
  exact on_post (two_taint [.x0] (pins_x0B FD.G fun a s h => by
    obtain ⟨D, X, hD, mi, hI, _⟩ := h; subst hD; exact hI.2.1.x0) (by taint_decide)) fun _ _ _ h => s6_s7 h

end ScalarRange

end VG.Proof.Ffdh.AArch64
