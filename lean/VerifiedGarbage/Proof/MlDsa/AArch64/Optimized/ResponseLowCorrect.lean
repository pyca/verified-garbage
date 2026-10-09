import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCore
import VerifiedGarbage.Spec.MlDsa.ResponseLow

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Round

theorem lowRun_return (m : Mem) (g B : Nat) (p a l : Addr) (hg : IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288) (ha : Reduced m p) (hb : RawReduced m a) :
    finishValue (lowRun m g B p a l 64).flags=if responseLowPass m p a g B then 1 else 0 := by
  have hflags := lowRun_flags m g B p a l hg hpl hap hal hB hB' ha hb (by decide : 64≤64)
  have hf := finishValue_flags hflags
  have he : (∀i<64,∀e<4,lowBad m g p a B i e=false) ↔ responseLowPass m p a g B := by
    simp only [lowBad,responseLowPass,responseDifference]
    constructor
    · intro h i hi
      change i<256 at hi
      have hh := h (i/4) (by omega) (i%4) (by omega)
      rw [show 4*(i/4)+i%4=i by omega] at hh
      exact Nat.lt_of_not_ge (of_decide_eq_false hh)
    · intro h i hi e he
      have hh := h (4*i+e) (by change 4*i+e<256; omega)
      exact decide_eq_false (by omega)
  have hr := finishValue_flags_range hflags
  by_cases h : responseLowPass m p a g B
  · rw [ite_eq_left h]; exact hf.mpr (he.mpr h)
  · rw [ite_eq_right h]
    exact hr.resolve_right (fun hone => h (he.mp (hf.mp hone)))

theorem subLowNorm_ok (s : State) (hg : IsG (arg32 s .x3))
    (hB : 1≤arg32 s .x4) (hB' : arg32 s .x4≤524288)
    (hcan : Reduced s.mem (s.gpr .x0)) (hraw : RawReduced s.mem (s.gpr .x1))
    (hpl : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)))
    (hap : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)))
    (hal : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)))
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s fun t =>
      Keep [.x0,.x1,.x2,.x3,.x5,.x9,.x10] s t ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=
        (highBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=
        lowBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
      t.gpr .x0=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0 := by
  refine WP.mono (subLowNorm_words_ok s hg hB (by simp only [arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]) ha hb hw hl) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).1]
    exact subHigh_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).2]
    exact subLow_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · rw [hret,lowRun_return _ _ _ _ _ _ hg hpl hap hal hB hB' hcan hraw]

end VG.Proof.MlDsa.AArch64.Optimized.Response
