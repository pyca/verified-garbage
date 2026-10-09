import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3] s t →
      (n≠0 → t.v .v2=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v3=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega)) (fun k hk => hr k (by omega)) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x1+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega)
    refine dotTerm_ok (ho n (by omega)) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
