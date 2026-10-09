import VerifiedGarbage.Spec.MlDsa.ResponseHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintContract

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem highBits_small {g : Nat} (hg : IsG g) (r : Zq) :
    0≤highBits g r ∧ highBits g r<44 := by
  rw [VG.Proof.MlDsa.Round.highBits_eq (mem_of_isG hg)]
  rcases hg with rfl | rfl <;>
    simp only [VG.Proof.MlDsa.Round.hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] <;> omega

theorem responseHintPoly_word {m : Mem} {low ct high : Addr} {g : Nat} (hg : IsG g)
    (hr : RawReduced m ct) (hp : ResponseDecomposed m low high g) {k : Nat} (hk : k<n) :
    hintWord (BitVec.ofNat 32 g) (reduceWord (coeffAt m ct k)+coeffAt m low k) (coeffAt m high k)=
      BitVec.ofNat 32 (responseHintPoly m low ct high g)[k]!.toNat := by
  rw [getElem!_pos (responseHintPoly m low ct high g) k hk]
  simp only [responseHintPoly,Vector.getElem_ofFn]
  apply hintWord_raw_field hg _ _ _ _ (hr k hk).1 (hr k hk).2 (hp k hk).1
  have hh := (hp k hk).2
  have hb := highBits_small hg (responseHintBase m low high g k)
  have hi := BitVec.toInt_eq_toNat_cond (coeffAt m high k)
  omega

theorem hintNorm_spec_ok (s : State) (g : Nat) (hg : IsG g)
    (hbreg : (s.gpr .x3).setWidth 32=BitVec.ofNat 32 g)
    (hr : RawReduced s.mem (s.gpr .x1))
    (hp : ResponseDecomposed s.mem (s.gpr .x0) (s.gpr .x2) g)
    (hd : (VG.Proof.MlDsa.AArch64.Arith.pR (s.gpr .x0)).Disjoint (VG.Proof.MlDsa.AArch64.Arith.pR (s.gpr .x1)))
    (he : (VG.Proof.MlDsa.AArch64.Arith.pR (s.gpr .x0)).Disjoint (VG.Proof.MlDsa.AArch64.Arith.pR (s.gpr .x2)))
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa Impl.MlDsa.AArch64.Optimized.Response.hintNorm s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x2,.x9,.x10] s t ∧
      HintIs t.mem (s.gpr .x0) 1 [responseHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) g] ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes [responseHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) g]+
        if normRq [signedPolyAt s.mem (s.gpr .x1)]<g then 4294967296 else 0) := by
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl | rfl <;> decide
  refine WP.mono (hintNorm_ok s g _ hgb.1 hgb.2 hbreg ha hb hh hw hd he hr
    (fun k hk => responseHintPoly_word hg hr hp hk)) fun t ⟨hk,_,hout,hcount,hvalid,hbound⟩ => ?_
  refine ⟨hk,hout,?_⟩
  have heq : (∀k<256,normZq (ofInt (coeffAt s.mem (s.gpr .x1) k).toInt)<g) ↔
      normRq [signedPolyAt s.mem (s.gpr .x1)]<g := by
    rw [VG.Proof.MlDsa.Round.normRq_lt]
    apply forall_congr'; intro k
    apply imp_congr_right; intro hk
    rw [getElem!_pos (signedPolyAt s.mem (s.gpr .x1)) k hk]
    simp only [signedPolyAt,Vector.getElem_ofFn]
  rw [heq] at hvalid
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  split
  · have hv := hvalid.mpr ‹_›
    have hc := hintCount_bound s.mem (BitVec.ofNat 32 g) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
    omega
  · have hv : (t.gpr .x0).toNat/4294967296=0 := by omega
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
