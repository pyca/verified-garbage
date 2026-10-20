module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reduce
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: divisibility and subgroup membership -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave redc aXc)

theorem ret_inner {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {r : Nat}
    (hc : SubCtx s B Z o w wx mi) (hr : r < 2 ^ 32) : WP isa (retInner r) s fun t =>
      t.gpr .rdi = B ∧ t.gpr .rax = BitVec.ofNat 64 r ∧ t.mem = s.mem ∧ Keep [.rdi, .rax] s t := by
  unfold retInner
  refine WP.seq (WP.mono (leave_ok hc) fun u ⟨hd, hm, k⟩ => ?_)
  exact WP.mono (ret_ok u hr) fun t ⟨ha, hm', kk⟩ =>
    ⟨(kk.gpr (by decide)).trans hd, ha, hm'.trans hm, (k.trans kk).mono (by decide)⟩

theorem prime_leave {p : CdP} {mi : BitVec 64} {s : State} (h : Work p mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (.block [leave]) s (StepPost p s (Parent p)) :=
  WP.mono (leave_ok (h.mem.ctx hd)) fun t ⟨hd', hm, k⟩ =>
    ⟨(h.keep hm k).parent hd', by rw [hm]; exact InScr.refl _ _ _,
      (fun _ _ => by rw [hm]), k.mono (by decide)⟩

private theorem divides_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (scan sQ ++ (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 ++
        ((wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl) ++
          (redc M.mm aX ++ ((isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa))) ++
            ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides, List.append_assoc, List.cons_append, List.nil_append]

theorem divides_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (hq : p.dl = 3 * p.k) (ho : p.Q % 2 = 1) (hQ : 1 < p.Q) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧
        t.gpr .rax = bit ((p.P - 1) % p.Q = 0 ∧ p.G ^ p.Q % p.P = 1)) := by
  rw [divides_eq]
  refine wp_seqs_cons (by simp [scan]) (WP.mono (prime_leave h hd) fun u₁ S₁ => ?_)
  refine wp_seqs_append (a := scan sQ) (by simp [scan]) (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1])
    (WP.mono (scan_order S₁.1 hq) fun u₂ S₂ => ?_)
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1]) (by simp [wsSetup])
    (WP.mono (scanned_minus S₂.1 (valid_facts hm h.base.k1).1) fun u₃ S₃ => ?_)
  refine wp_seqs_append (a := wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)
    (b := redc M.mm aX ++ ((isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa))) ++ ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))))
    (by simp [wsSetup]) (by simp [redc])
    (WP.mono (setup_order S₃.1.1 hq ho S₃.1.2) fun u₄ S₄ => ?_)
  obtain ⟨mi', hw₄⟩ := S₄.1
  refine wp_seqs_append (a := redc M.mm aX) (by simp [redc]) (by simp [isZero, ltArr, cmpArr])
    (WP.mono (reduce_order M hw₄ ho hQ) fun u₅ S₅ => ?_)
  refine wp_seqs_append (a := isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))
    (b := ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa)))
    (by simp [isZero, ltArr, cmpArr]) (by simp)
    (WP.mono (residue_test S₅.1) fun u₆ S₆ => ?_)
  have H := ((((S₁.trans S₂).trans S₃).trans S₄).trans S₅).trans S₆
  obtain ⟨⟨mi₆, hw₆, _⟩, hz₆⟩ := S₆.1
  simp only [seqs]
  refine WP.ite (!decide ((p.P - 1) % p.Q = 0)) (by simp [eval, hz₆]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬(p.P - 1) % p.Q = 0 := by simpa using hn
    refine WP.mono (ret_inner hw₆.ctx (r := 0) (by decide)) fun t ⟨hdi, ha, hmem, k⟩ => ?_
    exact ⟨⟨hdi, by simpa [bit, hn'] using ha⟩, by rw [hmem]; exact H.2.1,
      (fun i hi => by rw [hmem]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (k.mono (by decide))⟩
  · have hy' : (p.P - 1) % p.Q = 0 := by simpa using hy
    exact WP.mono (subgroup_ok M E R hw₆ hm hq) fun t S₇ =>
      ⟨⟨S₇.1.1, by simpa only [hy', true_and] using S₇.1.2⟩, (H.trans S₇).2⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
