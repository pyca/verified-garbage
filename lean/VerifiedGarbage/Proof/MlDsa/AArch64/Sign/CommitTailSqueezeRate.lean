import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBlock
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInitial

/-! ## From `CommitTailSqueezeWord.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep trn2_dwords stateReg_ne)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Proof.Sha3.AArch64 (WP.cons wp_str Upd)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Serialize a pair of high lanes without spilling the resident state. -/
theorem highPair_ok {s : State} {p : Addr} {i : Nat}
    (hi : i<8) (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block [.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
      .strq .v26 .x10 (16*i)]) s fun t => SqueezeKeep s t ∧
      t.mem=s.mem.write (p+BitVec.ofNat 64 (16*i)) 16
        (ofVDwords (vdword (s.v (vreg (2*i))) 1) (vdword (s.v (vreg (2*i+1))) 1)) := by
  refine wp_vop (d:=.v26) rfl fun a ha =>
    wp_strq ⟨by omega,by omega⟩ (by rw [ha.gpr,hp]) (by rw [ha.wr]; exact hout)
      fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ _ => by rw [ht.gpr,ha.gpr],fun r h26 _ => by rw [ht.v,ha.get r h26],
    ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp⟩,?_⟩
  rw [ht.mem,ha.v,ha.mem,trn2_dwords]

/-- The final high rate word is stored without touching any resident lane. -/
theorem highLast_ok {s : State} {p : Addr} (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+128) 8) :
    WP isa (.block [.umov .x .x7 .v16 1,.str .x .x7 .x10 128]) s fun t =>
      SqueezeKeep s t ∧ t.mem=s.mem.writeW (p+128) (vdword (s.v .v16) 1) := by
  refine WP.cons (s':=s.write .x .x7 (vdword (s.v .v16) 1)) rfl ?_
  have h := Upd.write64 s .x7 (vdword (s.v .v16) 1)
  refine wp_str (by decide) (by rw [h.other .x10 (by decide),hp])
    (by rw [h.wr]; exact hout) fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ hr => (congrFun ht.gpr r).trans (h.other r hr),
    fun r _ _ => by rw [ht.vec,h.vec],ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩,?_⟩
  rw [ht.mem,h.gpr,h.mem]
  rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSqueezeRate.lean` -/

section

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

end
