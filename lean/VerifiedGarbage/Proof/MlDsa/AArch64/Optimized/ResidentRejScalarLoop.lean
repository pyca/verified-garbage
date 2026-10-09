import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLoopState

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc)
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem candidateFold_one (m : Mem) (p : Addr) (L : List Zq) :
    candidateFold m p 1 L=acc L (candidate m p) := by
  change acc L (candidate m (p+BitVec.ofNat 64 0))=_
  rw [show p+BitVec.ofNat 64 0=p by bv_omega]

theorem scalarLoopStep_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (hd : d<n) (hc : (parsed s₀ b L d).length<256) :
    WP isa (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) s fun t =>
      ParseInv s₀ b p n L (d+1) t ∧ t.gpr .x16=t.gpr .x4*t.gpr .x5 := by
  refine WP.mono (scalarStep_ok
    (by rw [h.keep.rd,h.keep.wr,h.x2]; exact hl.read4 d hd)
    h.mask h.constants.qreg h.x3 h.x4 hc h.stored
    (by rw [h.keep.wr,h.x3]; exact hl.write4 _ hc))
    fun t ⟨ht,hvec,hf,h2,h5,h3,h4,hguard,hst⟩ => ?_
  have he := h.batch hl (by omega : d+1≤n) (by omega : (parsed s₀ b L d).length+1≤256)
  rw [candidateFold_one] at he
  rw [he] at h3 h4 hst
  refine ⟨⟨(h.keep.trans ht).mono (by decide),h.frame.trans hf,
    h.constants.of_keep ht (by decide) (by decide) hvec,by omega,?_,h3,h4,?_,?_,?_,hst⟩,hguard⟩
  · rw [h2,h.x2]
    change b+BitVec.ofNat 64 (3*d)+BitVec.ofNat 64 3=_
    rw [Offset.add_add,show 3*d+3=3*(d+1) by omega]
  · rw [h5,toNat_sub_n (by rw [h.x5]; simp; omega),h.x5,show (1 : BitVec 64).toNat=1 from rfl]
    omega
  · rw [ht.get .x10]; exact h.mask
  · rw [ht.get .x0]; exact h.zero

private theorem mulGuard_eval {s : State}
    (ha : (s.gpr .x4).toNat≤256) (hb : (s.gpr .x5).toNat≤336)
    (hg : s.gpr .x16=s.gpr .x4*s.gpr .x5) :
    isa.eval (.nonzero .x .x16) s=
      some (decide ((s.gpr .x4).toNat≠0 ∧ (s.gpr .x5).toNat≠0)) := by
  have ht : (s.gpr .x16).toNat=(s.gpr .x4).toNat*(s.gpr .x5).toNat := by
    rw [hg,BitVec.toNat_mul,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul ha hb) (by decide)
  have hz : s.gpr .x16=0 ↔ (s.gpr .x4).toNat=0 ∨ (s.gpr .x5).toNat=0 := by
    constructor
    · intro h
      have he := congrArg BitVec.toNat h
      rw [ht] at he
      exact Nat.mul_eq_zero.mp he
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [ht]
      exact Nat.mul_eq_zero.mpr h
  rw [eval_nonzero]
  by_cases h : s.gpr .x16=0
  · rw [h,decide_eq_false (by have:=hz.mp h; omega)]
    rfl
  · rw [show (s.gpr .x16 != 0)=true from bne_iff_ne.mpr h,
      decide_eq_true (by by_contra hn; apply h; exact hz.mpr (by omega))]

/-- The scalar remainder stops on exactly the original completion or input
exhaustion conditions. -/
theorem scalarLoop_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (hL : L.length≤256) (hd : d<n) (hc : (parsed s₀ b L d).length<256) :
    WP isa scalarLoop s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧
        (d'=n ∨ (parsed s₀ b L d').length=256) := by
  refine WP.loop (M := isa)
    (fun rank t => ∃j,rank=n-j ∧ ParseInv s₀ b p n L j t ∧ d≤j ∧
      j<n ∧ (parsed s₀ b L j).length<256) ?_
    (n-d) s ⟨d,rfl,h,Nat.le_refl _,hd,hc⟩
  rintro rank t ⟨j,rfl,ht,hdj,hj,hc⟩
  refine WP.mono (scalarLoopStep_ok hl ht hj hc) fun u ⟨hu,hflag⟩ => ?_
  have hb : (parsed s₀ b L (j+1)).length≤256 := rnFold_length_le hL _
  have he := mulGuard_eval (by rw [hu.x4]; omega) (by rw [hu.x5]; have:=hl.bound; omega) hflag
  rw [hu.x4,hu.x5] at he
  by_cases hp : j+1<n ∧ (parsed s₀ b L (j+1)).length<256
  · exact .inr ⟨by rw [he,decide_eq_true (by omega)],n-(j+1),by omega,j+1,rfl,hu,by omega,hp⟩
  · exact .inl ⟨by rw [he,decide_eq_false (by omega)],j+1,hu,by omega,by omega⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
