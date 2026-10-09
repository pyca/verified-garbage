import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Spec.MlDsa.ResponseZ

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem ofInt_nat (v : Nat) : ofInt (v:Int)=ofNat v := by
  apply Fin.ext
  change ((v:Int) % (q:Int)).toNat%q=v%q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

theorem zSum_coeff (m : Mem) (p a : Addr) {k : Nat} (hk : k<n) :
    (add (polyAt m p) (signedPolyAt m a))[k]! =
      ofInt (((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt) := by
  rw [add_get _ _ hk,polyAt_get _ _ hk,ofInt_add,ofInt_nat]
  congr 1
  rw [getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]

theorem zRun_centered (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    CenteredReduced (zRun m p a B 64).mem p := by
  intro k hk
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  have hak : (coeffAt m p k).toNat<8380417 := ha k hk
  have hbk : -8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<16760834 := hb k hk
  have := reduce32_bounds (x := ((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt)
    (by omega) (by omega)
  change -8380417<_ ∧ _<8380417
  omega

theorem zRun_poly (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    signedPolyAt (zRun m p a B 64).mem p=add (polyAt m p) (signedPolyAt m a) := by
  apply ext_getElem!
  intro k hk
  rw [zSum_coeff _ _ _ hk,getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  unfold ofInt
  congr 1
  exact congrArg Int.toNat (reduce32_mod _)

theorem zRun_finish (m : Mem) (p a : Addr) (B : Nat)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a)
    (hB : 1≤B) (hB' : B≤524288) :
    finishValue (zRun m p a (BitVec.ofNat 32 B) 64).flags=
      if normRq [add (polyAt m p) (signedPolyAt m a)]<B then 1 else 0 := by
  have hf := zRun_flags m p a B hd hB hB' ha hb (by decide : 64≤64)
  have he := finishValue_flags hf
  have hr := finishValue_flags_range hf
  have hn : (∀i<64,∀e<4,zBad m p a B i e=false) ↔ normRq [add (polyAt m p) (signedPolyAt m a)]<B := by
    rw [VG.Proof.MlDsa.Round.normRq_lt]
    constructor
    · intro h k hk
      have hg := h (k/4) (by change k<256 at hk; omega) (k%4) (by omega)
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le] at hg
      rw [show 4*(k/4)+k%4=k by omega] at hg
      rw [zSum_coeff _ _ _ hk]
      exact hg
    · intro h i hi e he
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le]
      have hk : 4*i+e<n := by rw [n_eq]; omega
      rw [← zSum_coeff _ _ _ hk]
      exact h _ hk
  rw [hn] at he
  split
  · exact he.mpr ‹_›
  · rcases hr with hr|hr
    · exact hr
    · exact False.elim (‹¬_› (he.mp hr))

theorem addNorm_ok (s : State)
    (hd : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)))
    (hay : Reduced s.mem (s.gpr .x0)) (hbs : RawReduced s.mem (s.gpr .x1))
    (hB : 1≤((s.gpr .x2).setWidth 32).toNat) (hB' : ((s.gpr .x2).setWidth 32).toNat≤524288)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x9,.x10] s t ∧
      CenteredReduced t.mem (s.gpr .x0) ∧
      signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
      t.gpr .x0=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
        ((s.gpr .x2).setWidth 32).toNat then 1 else 0 := by
  refine WP.mono (addNorm_words_ok s ha hb hw) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · rw [hm]; exact zRun_centered _ _ _ _ hd hay hbs
  · rw [hm]; exact zRun_poly _ _ _ _ hd hay hbs
  · rw [hret]
    have h := zRun_finish s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32).toNat hd hay hbs hB hB'
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h

end VG.Proof.MlDsa.AArch64.Optimized.Response
