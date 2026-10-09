import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotLoad

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19] s t →
      (n≠0 → t.v .v18=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v19=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega)) (fun k hk => hr k (by omega)) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x13+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega)
    refine dotTerm_ok (ho n (by omega)) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

theorem dotLoad_ok {n : Nat} (hn : 0<n) {d : VReg} (h30 : d≠.v30) (h31 : d≠.v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19,.v20,d] s t → ProductConstants t →
      (∀e<4,vword (t.v d) e=centeredDot (fun k => dotInput s .x13 off k e)
        (fun k => dotInput s .x14 off k e) n) → WP isa (.block rest) t Q) :
    WP isa (.block (dotLoad n d off++rest)) s Q := by
  unfold dotLoad
  rw [List.append_assoc]
  refine dotTerms_ok n ho hr fun a ha e18 e19 => ?_
  have ca := hc.chg ha (by decide) (by decide)
  refine dotReduce_ok h31 (dotAccum s off n) (e18 (by omega)) (e19 (by omega)) ca.qv ca.qiv
    fun t ht ev => ?_
  have h : VChg [.v16,.v17,.v18,.v19,.v20,d] s t := (ha.trans ht).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  exact next t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ev

end VG.Proof.MlDsa.AArch64.Optimized
