module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH private-key validation on x86-64: choose the scalar's bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

abbrev KpP.upper (p : KpP) : Nat := p.params.q.getD (p.P - 1)

def BoundPost (p : KpP) (xb : List Byte) (mi : BitVec 64) (s t : State) : Prop :=
  Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧ t.gpr .rax = bit (Spec.Rsa.os2ip xb < p.upper) ∧
    word t.mem (off p.B (inner p.w)) (8 * sF) = word s.mem (off p.B (inner p.w)) (8 * sF)

private theorem ltQ_work {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (loadArr aY sQ sK ++ ltArr aXm aY)) s (StepPost p s fun t => Work p xb mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ t.gpr .rax = bit (Spec.Rsa.os2ip xb < p.Q) ∧
      word t.mem (off p.B (inner p.w)) (8 * sF) = word s.mem (off p.B (inner p.w)) (8 * sF)) := by
  refine wp_seqs_append (a := loadArr aY sQ sK) (by simp [loadArr]) (by simp [ltArr, cmpArr])
    (WP.mono (loadQ_work h hd hq) fun u ⟨⟨hw, hdi, hy, hF⟩, hi, hs, k⟩ => ?_)
  have hc := hw.mem.ctx hdi
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact WP.mono (ltArr_ok hc.good (Nat.le_refl _) (by omega) (by omega)
    (show aXm < 8 by decide) (show aY < 8 by decide)) fun t ⟨ha, hm, kk⟩ =>
      ⟨⟨hw.keep hm kk, (kk.gpr (by decide)).trans hdi, by rwa [hw.x, hy] at ha,
        by rw [hm]; exact hF⟩, by rw [hm]; exact hi,
        (fun i hi => by rw [hm]; exact hs i hi), keep_trans k (kk.mono (by decide))⟩

private theorem noQ_enter {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = p.B) (hodd : p.P % 2 = 1) (hq : p.dl = 2 * p.k) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm)) s (StepPost p s (BoundPost p xb mi s)) := by
  change WP isa (.seq (.block [enter]) (seqs (ltP aXm))) s _
  refine WP.seq (WP.mono (h.enter hd) fun u ⟨hw, hdi, hm, k⟩ => ?_)
  exact WP.mono (ltP_work hw hdi hodd) fun t ⟨⟨hw', hd', ha, hF⟩, hi, hs, kk⟩ =>
    ⟨⟨hw', hd', by simpa only [KpP.upper, h.base.params_none hq, Option.getD_none] using ha,
      by rw [hm] at hF; exact hF⟩, by rw [hm] at hi; exact hi,
      (fun i hi => by rw [hs i hi, hm]), keep_trans (k.mono (by decide)) kk⟩

private theorem withQ_enter {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = p.B) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ loadArr aY sQ sK ++ ltArr aXm aY)) s
      (StepPost p s (BoundPost p xb mi s)) := by
  change WP isa (.seq (.block [enter]) (seqs (loadArr aY sQ sK ++ ltArr aXm aY))) s _
  refine WP.seq (WP.mono (h.enter hd) fun u ⟨hw, hdi, hm, k⟩ => ?_)
  exact WP.mono (ltQ_work hw hdi hq) fun t ⟨⟨hw', hd', ha, hF⟩, hi, hs, kk⟩ =>
    ⟨⟨hw', hd', by simpa only [KpP.upper, h.base.params_some hq, Option.getD_some] using ha,
      by rw [hm] at hF; exact hF⟩, by rw [hm] at hi; exact hi,
      (fun i hi => by rw [hs i hi, hm]), keep_trans (k.mono (by decide)) kk⟩

theorem bound_ok {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = p.B) (hz : s.zf = some (decide (p.dl = 2 * p.k))) (ho : p.P % 2 = 1) :
    WP isa (.ite .e (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ loadArr aY sQ sK ++ ltArr aXm aY))) s
      (StepPost p s (BoundPost p xb mi s)) := by
  refine WP.ite (decide (p.dl = 2 * p.k)) (by simp [eval, hz]) (fun hq => ?_) (fun hq => ?_)
  · exact noQ_enter h hd ho (of_decide_eq_true hq)
  · have he : p.dl = 3 * p.k := by
      have hn := of_decide_eq_false hq
      rcases h.base.dl with h | h <;> omega
    exact withQ_enter h hd he

end VG.Proof.Ffdh.X86_64.CheckPrivate
