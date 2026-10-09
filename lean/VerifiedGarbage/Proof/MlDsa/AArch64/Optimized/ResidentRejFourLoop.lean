import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLoopState

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem fourLoopStep_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=4) (hd : d+4≤n) (hc : (parsed s₀ b L d).length+4≤256) :
    WP isa vectorBody s fun t => ParseInv s₀ b p n L (d+4) t ∧ t.gpr .x17=4 ∧
      t.gpr .x16=(if 4≤256-(parsed s₀ b L (d+4)).length then t.gpr .x5 else 0) := by
  refine WP.mono (fourBody_ok h.constants h17 h.zero
    (by rw [h.keep.rd,h.keep.wr,h.x2]; exact hl.read16 _ (by omega))
    h.x3 h.x4 hc h.stored (fun i hi => by rw [h.keep.wr]; exact hl.write4 i hi)
    (by rw [h.keep.wr,h.x3]; exact hl.write16 _ hc))
    fun t ⟨ht,hf,hconst,h2,h5,h3,h4,hguard,hst⟩ => ?_
  have he := h.batch hl hd hc
  rw [he] at h3 h4 hst
  have hn5 : (t.gpr .x5).toNat=n-(d+4) := by
    rw [h5,toNat_sub_n (by rw [h.x5]; simp; omega),h.x5,show (4 : BitVec 64).toNat=4 from rfl]
    omega
  refine ⟨⟨(h.keep.trans ht).mono (by decide),h.frame.trans hf,hconst,hd,?_,h3,h4,hn5,?_,?_,hst⟩,
    by rw [ht.get .x17]; exact h17,?_⟩
  · rw [h2,h.x2]
    change b+BitVec.ofNat 64 (3*d)+BitVec.ofNat 64 12=_
    rw [Offset.add_add,show 3*d+12=3*(d+4) by omega]
  · rw [ht.get .x10]; exact h.mask
  · rw [ht.get .x0]; exact h.zero
  · rw [hguard,h4]

private theorem fourGuard_eval {s : State} {cap rem : Nat}
    (hg : s.gpr .x16=if 4≤cap then s.gpr .x5 else 0)
    (hr : (s.gpr .x5).toNat=rem) :
    isa.eval (.nonzero .x .x16) s=some (decide (4≤cap ∧ rem≠0)) := by
  rw [eval_nonzero,hg]
  by_cases hc : 4≤cap
  · rw [ite_eq_left hc]
    simp only [hc,true_and]
    by_cases hz : s.gpr .x5=0
    · have hr0 : rem=0 := by rw [←hr,hz]; rfl
      rw [hz,hr0]
      rfl
    · have hr0 : rem≠0 := by
        intro h
        apply hz
        apply BitVec.eq_of_toNat_eq
        rw [hr,h]
        rfl
      rw [show (s.gpr .x5 != 0)=true from bne_iff_ne.mpr hz,decide_eq_true hr0]
  · rw [ite_eq_right hc]
    simp only [hc,false_and,decide_false]
    rfl

/-- Divisibility of the segment length ensures every nonempty vector tail
has at least four candidates available. -/
theorem fourLoop_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=4) (hd : d+4≤n) (hc : (parsed s₀ b L d).length+4≤256)
    (hmod : n%4=d%4) :
    WP isa (.loop vectorBody (.nonzero .x .x16)) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧ n%4=d'%4 ∧ t.gpr .x17=4 ∧
        (d'=n ∨ 256<(parsed s₀ b L d').length+4) := by
  refine WP.loop (M := isa)
    (fun rank t => ∃j,rank=n-j ∧ ParseInv s₀ b p n L j t ∧ d≤j ∧ n%4=j%4 ∧
      t.gpr .x17=4 ∧ j+4≤n ∧ (parsed s₀ b L j).length+4≤256) ?_
    (n-d) s ⟨d,rfl,h,Nat.le_refl _,hmod,h17,hd,hc⟩
  rintro rank t ⟨j,rfl,ht,hdj,hmod,h17,hj,hc⟩
  refine WP.mono (fourLoopStep_ok hl ht h17 hj hc) fun u ⟨hu,h17,hflag⟩ => ?_
  have he := fourGuard_eval hflag hu.x5
  by_cases hp : j+4<n ∧ (parsed s₀ b L (j+4)).length+4≤256
  · refine .inr ⟨?_,n-(j+4),by omega,j+4,rfl,hu,by omega,by omega,h17,by omega,hp.2⟩
    rw [he,decide_eq_true (by omega)]
  · refine .inl ⟨?_,j+4,hu,by omega,by omega,h17,by omega⟩
    rw [he,decide_eq_false (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
