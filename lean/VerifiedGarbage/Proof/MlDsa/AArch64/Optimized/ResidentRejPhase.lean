import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem ParseInv.of_control {s₀ s t : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) (hk : Only [.x16,.x17] s t) (hv : t.v=s.v) :
    ParseInv s₀ b p n L d t := by
  refine ⟨(h.keep.trans hk.keep).mono (by decide),by rw [hk.mem]; exact h.frame,
    h.constants.of_keep hk.keep (by decide) (by decide) hv,h.bound,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hk.get .x2]; exact h.x2
  · rw [hk.get .x3]; exact h.x3
  · rw [hk.get .x4]; exact h.x4
  · rw [hk.get .x5]; exact h.x5
  · rw [hk.get .x10]; exact h.mask
  · rw [hk.get .x0]; exact h.zero
  · rw [hk.mem]; exact h.stored

theorem parsed_done (s : State) (b : Addr) (L : List Zq) {d n : Nat}
    (hd : d≤n) (h : d=n ∨ (parsed s b L d).length=256) : parsed s b L d=parsed s b L n := by
  rcases h with rfl | hf
  · rfl
  · conv_rhs => rw [show n=d+(n-d) by omega]
    unfold parsed at hf ⊢
    rw [candidateBytes_append,rnFold_append _ _ _ (by rw [candidateBytes_length]; omega),
      rnFold_full hf]

theorem widePhase_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=16)
    (hg : s.gpr .x16=if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0) :
    WP isa (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16))) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧ d'%4=d%4 ∧ t.gpr .x17=16 ∧
        (n<d'+16 ∨ 256<(parsed s₀ b L d').length+16) := by
  rw [h.x4,h.x5] at hg
  by_cases hp : d+16≤n ∧ (parsed s₀ b L d).length+16≤256
  · refine WP.ite false (by rw [eval_zero,hg,ite_eq_left (by omega)]; rfl)
      (fun h => nomatch h) (fun _ => wideLoop_ok hl h h17 hp.1 hp.2)
  · refine WP.ite true (by rw [eval_zero,hg,ite_eq_right (by omega)]; rfl)
      (fun _ => WP.block_nil_iff.mpr ⟨d,h,Nat.le_refl _,rfl,h17,by omega⟩) (fun h => nomatch h)

theorem fourPhase_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (h17 : s.gpr .x17=4) (hmod : n%4=d%4)
    (hg : s.gpr .x16=if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0) :
    WP isa (.ite (.zero .x .x16) (.block []) (.loop vectorBody (.nonzero .x .x16))) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧ n%4=d'%4 ∧ t.gpr .x17=4 ∧
        (d'=n ∨ 256<(parsed s₀ b L d').length+4) := by
  rw [h.x4] at hg
  by_cases hp : d<n ∧ (parsed s₀ b L d).length+4≤256
  · have hn : s.gpr .x5≠0 := by
      intro he
      have hh := congrArg BitVec.toNat he
      rw [h.x5] at hh
      change n-d=0 at hh
      omega
    refine WP.ite false (by rw [eval_zero,hg,ite_eq_left (by omega),show (s.gpr .x5 == 0)=false from beq_eq_false_iff_ne.mpr hn])
      (fun h => nomatch h) (fun _ => fourLoop_ok hl h h17 (by have:=h.bound; omega) hp.2 hmod)
  · have hz : s.gpr .x16=0 := by
      rw [hg]
      split
      · apply BitVec.eq_of_toNat_eq
        rw [h.x5]
        change n-d=0
        have:=h.bound
        omega
      · rfl
    refine WP.ite true (by rw [eval_zero,hz]; rfl)
      (fun _ => WP.block_nil_iff.mpr ⟨d,h,Nat.le_refl _,hmod,h17,by have:=h.bound; omega⟩)
      (fun h => nomatch h)

/-- The final scalar phase is skipped exactly when the output is full or
there is no input left. -/
theorem scalarPhase_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s) (hL : L.length≤256) :
    WP isa (.seq (.block [.mul .x .x16 .x4 .x5])
      (.ite (.zero .x .x16) (.block []) scalarLoop)) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧
        (d'=n ∨ (parsed s₀ b L d').length=256) := by
  have hm : WP isa (.block [.mul .x .x16 .x4 .x5]) s fun t =>
      Only [.x16] s t ∧ t.gpr .x16=s.gpr .x4*s.gpr .x5 :=
    wp_mul fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.seq (WP.mono (WP.keepV (by decide) hm) fun a ⟨⟨ha,h16⟩,hv⟩ => ?_)
  have hi := h.of_control (ha.mono (by decide)) hv
  have hb : (parsed s₀ b L d).length≤256 := rnFold_length_le hL _
  have hval : (a.gpr .x16).toNat=(256-(parsed s₀ b L d).length)*(n-d) := by
    rw [h16,toNat_mul_n (by
      have h4b : (s.gpr .x4).toNat≤256 := by rw [h.x4]; omega
      have h5b : (s.gpr .x5).toNat≤336 := by rw [h.x5]; have:=hl.bound; omega
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul h4b h5b) (by decide)),h.x4,h.x5]
  have he : isa.eval (.zero .x .x16) a=
      some (decide (d=n ∨ (parsed s₀ b L d).length=256)) := by
    rw [eval_zero,eq_zero_iff,hval]
    congr 1
    apply decide_eq_decide.mpr
    rw [Nat.mul_eq_zero]
    have:=h.bound
    omega
  by_cases hd : d=n ∨ (parsed s₀ b L d).length=256
  · exact WP.ite true (by rw [he,decide_eq_true hd])
      (fun _ => WP.block_nil_iff.mpr ⟨d,hi,Nat.le_refl _,hd⟩) (fun h => nomatch h)
  · exact WP.ite false (by rw [he,decide_eq_false hd]) (fun h => nomatch h)
      (fun _ => scalarLoop_ok hl hi hL (by have:=h.bound; omega) (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
