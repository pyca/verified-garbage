import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLoopState

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem wideLoopStep_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=16) (hd : d+16≤n) (hc : (parsed s₀ b L d).length+16≤256) :
    WP isa wideBody s fun t => ParseInv s₀ b p n L (d+16) t ∧ t.gpr .x17=16 ∧
      t.gpr .x16=(if 16≤256-(parsed s₀ b L (d+16)).length ∧ 16≤n-(d+16) then 16 else 0) := by
  have hr : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16 := by
    intro j hj
    rw [h.keep.rd,h.keep.wr,h.x2,Offset.add_add,show 3*d+12*j=3*(d+4*j) by omega]
    exact hl.read16 _ (by omega)
  have hw16 : ∀j<4,InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*j)) 16 := by
    intro j hj
    rw [h.keep.wr,h.x3]
    have he : coeffAddr p (parsed s₀ b L d).length+BitVec.ofNat 64 (16*j)=
        coeffAddr p ((parsed s₀ b L d).length+4*j) := by
      unfold coeffAddr
      rw [Offset.add_add]
      congr 2 <;> omega
    rw [he]
    exact hl.write16 _ (by omega)
  refine WP.mono (wideBody_ok h.constants h17 h.zero hr h.x3 h.x4 hc h.stored
    (fun i hi => by rw [h.keep.wr]; exact hl.write4 i hi) hw16)
    fun t ⟨ht,hf,hconst,h2,h5,h3,h4,hguard,hst⟩ => ?_
  have he := h.batch hl hd hc
  rw [he] at h3 h4 hst
  have hn5 : (t.gpr .x5).toNat=n-(d+16) := by
    rw [h5,toNat_sub_n (by rw [h.x5]; simp; omega),h.x5,show (16 : BitVec 64).toNat=16 from rfl]
    omega
  refine ⟨⟨(h.keep.trans ht).mono (by decide),h.frame.trans hf,hconst,hd,?_,h3,h4,hn5,?_,?_,hst⟩,
    by rw [ht.get .x17]; exact h17,?_⟩
  · rw [h2,h.x2]
    change b+BitVec.ofNat 64 (3*d)+BitVec.ofNat 64 48=_
    rw [Offset.add_add,show 3*d+48=3*(d+16) by omega]
  · rw [ht.get .x10]; exact h.mask
  · rw [ht.get .x0]; exact h.zero
  · rw [hguard,h4,hn5]

/-- The wide loop stops only when fewer than sixteen input candidates or
output slots remain. Its rank is the finite number of unconsumed inputs. -/
theorem wideLoop_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=16) (hd : d+16≤n) (hc : (parsed s₀ b L d).length+16≤256) :
    WP isa (.loop wideBody (.nonzero .x .x16)) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧ d'%4=d%4 ∧ t.gpr .x17=16 ∧
        (n<d'+16 ∨ 256<(parsed s₀ b L d').length+16) := by
  refine WP.loop (M := isa)
    (fun rank t => ∃j,rank=n-j ∧ ParseInv s₀ b p n L j t ∧ d≤j ∧ j%4=d%4 ∧
      t.gpr .x17=16 ∧ j+16≤n ∧ (parsed s₀ b L j).length+16≤256) ?_
    (n-d) s ⟨d,rfl,h,Nat.le_refl _,rfl,h17,hd,hc⟩
  rintro rank t ⟨j,rfl,ht,hdj,hmod,h17,hj,hc⟩
  refine WP.mono (wideLoopStep_ok hl ht h17 hj hc) fun u ⟨hu,h17,hflag⟩ => ?_
  by_cases hp : j+16+16≤n ∧ (parsed s₀ b L (j+16)).length+16≤256
  · refine .inr ⟨?_,n-(j+16),by omega,j+16,rfl,hu,by omega,by omega,h17,hp⟩
    rw [eval_nonzero,hflag,ite_eq_left (by omega)]
    rfl
  · refine .inl ⟨?_,j+16,hu,by omega,by omega,h17,by omega⟩
    rw [eval_nonzero,hflag,ite_eq_right (by omega)]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
