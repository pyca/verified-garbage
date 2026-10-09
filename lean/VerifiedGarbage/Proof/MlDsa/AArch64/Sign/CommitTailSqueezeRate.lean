import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSqueezeWord

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep RatePairs RateBlock)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

theorem highPairs_ok {s : State} {p : Addr} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (hptr : s.gpr .x10=p)
    (hout : ∀i<8, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      ([.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
        .strq .v26 .x10 (16*i)] : List Instr))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RatePairs t.mem p 8 B ∧ Frame [⟨p,128⟩] s.mem t.mem := by
  refine WP.mono (wp_range_flatMap (M:=isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem p k B ∧ Frame [⟨p,128⟩] s.mem t.mem)
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,Frame.refl _ _⟩)
    fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2⟩
  have hpt := ht.1.pairs hp
  refine WP.mono (highPair_ok hk ((ht.1.gpr .x10 (by decide) (by decide)).trans hptr)
    (by rw [ht.1.wr]; exact hout k hk)) fun u hu => ?_
  have hm : u.mem=t.mem.write (p+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega),hpt _ (by omega),vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_⟩
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.1 i (by omega)
  · rw [hm]
    exact ht.2.2.write (r:=⟨p,128⟩) (by simp) _ (Offset.contains_base p (by omega) (by omega))

/-- One 136-byte high-lane squeeze preserves both resident permutation states. -/
theorem highRate_ok {s : State} {p : Addr} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (hptr : s.gpr .x10=p)
    (hout : ∀i<8, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16)
    (hlast : InRegions s.wr (p+128) 8) :
    WP isa (.block (((List.range 8).flatMap fun i =>
      ([.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
        .strq .v26 .x10 (16*i)] : List Instr)) ++
      ([.umov .x .x7 .v16 1,.str .x .x7 .x10 128] : List Instr))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RateBlock t.mem p 8 B ∧ Frame [⟨p,136⟩] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (highPairs_ok hp hptr hout) fun a ha => ?_
  refine WP.mono (highLast_ok ((ha.1.gpr .x10 (by decide) (by decide)).trans hptr)
    (by rw [ha.1.wr]; exact hlast)) fun t ht => ?_
  have hm : t.mem=a.mem.writeW (p+128) B[16]! := by
    have hp16 : a.v .v16=ofVDwords A[16]! B[16]! := ha.2.1 16 (by decide)
    rw [ht.2,hp16,vdword_ofVDwords_1]
  refine ⟨ha.1.trans ht.1,ht.1.pairs ha.2.1,⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hm]
    change (a.mem.write (p+BitVec.ofNat 64 128) 8 B[16]!).read (p+BitVec.ofNat 64 (16*i)) 16=_
    rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=128) (k:=8)
      (by omega) (by omega) (by omega)) (by decide)]
    exact ha.2.2.1 i hi
  · change t.mem.readW (p+128) 64=B[16]!
    rw [hm,Mem.readW_writeW_self64]
  · rw [hm]
    have hf : Frame [⟨p,136⟩] s.mem a.mem := ha.2.2.2.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨p,136⟩,by simp,by simpa using Offset.sub_base p (d:=0) (n:=128) (k:=136) (by decide)⟩)
    exact hf.writeW (r:=⟨p,136⟩) (by simp) _ (Offset.contains_base p (by decide) (by decide))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
