import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (polyR)
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored)

/-- The resumed squeeze keeps the parser's spilled registers and its polynomial. -/
theorem resume_call_ok (v : Proof.Sha3.AArch64.Permutation) {P : Sp} {σ s : State}
    {c : Spec.MlDsa.IPoly} {w9 w10 w11 : BitVec 64} {pos : Nat} {Y : List Byte}
    (hp : SpOk P σ) (he : Env P σ s) (ha : SqueezeArgs P.scr pos s) (hpos : pos≤136)
    (hn : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) pos 136=Y)
    (hs : Saved P.scr w9 w10 w11 s) (hc : CStored s.mem P.a c) :
    WP isa (.call ("vg_keccak_squeeze_scratch"++v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s fun u =>
      Env P σ u ∧ Saved P.scr w9 w10 w11 u ∧ CStored u.mem P.a c ∧
      bytesAt u.mem (P.at' 840) 136=Y := by
  have cw : Covers [⟨P.scr,200⟩,⟨P.at' 840,136⟩,⟨P.at' 200,640⟩] s.wr :=
    cov_scr hp he.wr fun r hr => by
      rcases mem3 hr with rfl|rfl|rfl
      · exact ⟨0,(at_zero).symm,by simp⟩
      · exact ⟨840,rfl,by simp⟩
      · exact ⟨200,rfl,by simp⟩
  refine squeeze_callWith v (st := P.scr) (out := P.at' 840) (sc := P.at' 200)
    (rate := 136) (pos := pos) (len := 136) ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 ha.x5 (by decide) hpos
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (disj_scr (.inr (by omega)) (by omega) (by omega))
    (by rw [he.sp]; exact hp.sp16) (by rw [stk,he.sp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk,he.sp]; exact stk_scr' hp (by omega)) (by rw [stk,he.sp]; exact stk_scr' hp (by omega))
    (cov_rd cw) cw fun u hk hout _ _ => ?_
  refine ⟨he.call hp hk ?_,hs.keep hk.frame ?_,stored_frame hc hk.frame ?_,hout.trans hn⟩
  · intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact .inl ⟨0,200,by rw [at_zero],by decide⟩
    · exact .inl ⟨840,136,rfl,by decide⟩
    · exact .inl ⟨200,640,rfl,by decide⟩
    · exact .inr rfl
  · intro d hd r hr
    have hd0 : 1800≤d ∧ d≤1816 := by
      rcases mem3 hd with rfl | rfl | rfl <;> omega
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · simpa only [at_zero] using (disj_scr (P := P) (a := d) (n := 8) (b := 0) (m := 200) (.inr (by omega)) (by omega) (by omega))
    · exact disj_scr (P := P) (a := d) (n := 8) (b := 840) (m := 136) (.inr (by omega)) (by omega) (by omega)
    · exact disj_scr (P := P) (a := d) (n := 8) (b := 200) (m := 640) (.inr (by omega)) (by omega) (by omega)
    · rw [he.sp]; exact (stk_scr' hp (a := d) (n := 8) (by omega)).symm
  · intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact hp.a_scr.sub_right (sub_scr0 (by decide))
    · exact a_scr' hp (by decide)
    · exact a_scr' hp (by decide)
    · rw [he.sp]; exact hp.stk_a.symm
end VG.Proof.MlDsa.AArch64.Optimized.Ball
