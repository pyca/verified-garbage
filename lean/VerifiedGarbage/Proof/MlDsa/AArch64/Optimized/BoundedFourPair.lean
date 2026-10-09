import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueeze

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem pair_ok (sha3 : Bool) {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hp16 : rp ≠ .x16)
    (hpair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwp : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwa : ∀ i < 17, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 17, InRegions s.wr (outAddr b i) 8)
    (hd : (rateR a).Disjoint (rateR b))
    (hpa : (pairR p).Disjoint (rateR a)) (hpb : (pairR p).Disjoint (rateR b)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 rp ra rb) s fun t =>
      BlockKeep s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate136 t.mem a (Spec.Sha3.keccakF A) ∧ Rate136 t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,rateR a,rateR b] s.mem t.mem := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.pair
  refine WP.seq (WP.mono (load_ok hp hpair hin) fun s1 ⟨h1,hpair1⟩ => ?_)
  refine WP.seq (WP.mono (roundsProg_ok sha3 (by decide : 24 ≤ 24) hpair1) fun s2 ⟨h2,hpair2⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ((h2.gpr rp hp16).trans ((congrFun h1.gpr rp).trans hp)) hpair2
    (fun i hi => by rw [h2.wr,h1.wr]; exact hwp i hi)) fun s3 ⟨h3,hpair3,hf3⟩ => ?_
  refine WP.mono (squeeze136_ok (A := Spec.Sha3.keccakF A) (B := Spec.Sha3.keccakF B)
    (by rw [h3.gpr,h2.gpr ra ha16,h1.gpr,ha])
    (by rw [h3.gpr,h2.gpr rb hb16,h1.gpr,hb]) ha6 ha7 hb6 hb7
    (by intro i hi; rw [h3.v]; exact hpair2 i hi) hd
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwa i hi)
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwb i hi)) fun t ⟨h4,hra,hrb,hf4⟩ => ?_
  refine ⟨⟨fun r h6 h7 h16 => by rw [h4.gpr r h6 h7,h3.gpr,h2.gpr r h16,h1.gpr],
    h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd)),
    h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr)),
    h4.sp.trans (h3.sp.trans (h2.sp.trans h1.sp))⟩,?_,hra,hrb,?_⟩
  · intro i hi
    rw [hf4.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exact hpa; exact hpb) (by decide)]
    exact hpair3 i hi
  · have hf3' : Frame [pairR p,rateR a,rateR b] s.mem s3.mem := by
      rw [← h1.mem,← h2.mem]
      exact hf3.sub (fun r hr => ⟨r,by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self,fun _ h => h⟩)
    exact hf3'.trans (hf4.sub (fun r hr => ⟨r,List.mem_cons_of_mem _ hr,fun _ h => h⟩))
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
