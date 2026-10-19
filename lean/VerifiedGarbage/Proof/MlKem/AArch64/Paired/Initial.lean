module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitialOne
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def initialCode (a b : Nat) (w16 : Bool := false) : Prog isa := seqs [Paired.reject 400 a .x22 w16,
  .block [.str .x .x3 .x19 1680,.str .x .x4 .x19 1688],Paired.reject 904 b .x23 w16,
  .block [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704],.block [.logic .and .x .x6 .x22 .x23]]

def initialRegions (p a b : Addr) : List Region :=
 [polyRegion a,polyRegion b,⟨p+BitVec.ofNat 64 1680,16⟩,⟨p+BitVec.ofNat 64 1696,16⟩]

structure InitialPostW (w16 : Bool) (A B : Nat→Byte) (p a b : Addr) (s t : State) : Prop where
  keep : Keep [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x22,.x23] s t
  frame : Frame (initialRegions p a b) s.mem t.mem
  first : Rej8.Scalar.CoeffsW w16 t.mem a (sampleAfter [] A 168)
  second : Rej8.Scalar.CoeffsW w16 t.mem b (sampleAfter [] B 168)
  savedA : checkpointW w16 (p+BitVec.ofNat 64 1680) a (sampleAfter [] A 168) t.mem
  savedB : checkpointW w16 (p+BitVec.ofNat 64 1696) b (sampleAfter [] B 168) t.mem
  flagA : (t.gpr .x22).toNat=if (sampleAfter [] A 168).length=256 then 1 else 0
  flagB : (t.gpr .x23).toNat=if (sampleAfter [] B 168).length=256 then 1 else 0
  both : (t.gpr .x6).toNat=if (sampleAfter [] A 168).length=256 ∧ (sampleAfter [] B 168).length=256 then 1 else 0
  constants : Rej8.Constants t

theorem initial_ok {w16 : Bool} {s : State} {a b : Nat} (ha : a<65536) (hb : b<65536)
    {A B : Nat→Byte}
    (pa : Rej8.EnvW w16 168 A (s.gpr .x19+BitVec.ofNat 64 400) (s.gpr .x28+BitVec.ofNat 64 a) s)
    (pb : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 904) (s.gpr .x28+BitVec.ofNat 64 b) s)
    (hc : Rej8.Constants s) (hs : Covers [⟨s.gpr .x19,2048⟩] s.wr)
    (da : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint ⟨s.gpr .x19,2048⟩)
    (db : (polyRegion (s.gpr .x28+BitVec.ofNat 64 b)).Disjoint ⟨s.gpr .x19,2048⟩)
    (dab : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 b)))
    (dt : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨s.gpr .x19,2048⟩) :
    WP isa (initialCode a b w16) s
      (InitialPostW w16 A B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s) := by
  have cpA : Region.Sub ⟨s.gpr .x19+BitVec.ofNat 64 1680,16⟩ ⟨s.gpr .x19,2048⟩ := Offset.sub_base _ (by decide)
  have cpB : Region.Sub ⟨s.gpr .x19+BitVec.ofNat 64 1696,16⟩ ⟨s.gpr .x19,2048⟩ := Offset.sub_base _ (by decide)
  have cpAB : (Region.mk (s.gpr .x19+BitVec.ofNat 64 1680) 16).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 1696,16⟩ :=
    Offset.disjoint (s.gpr .x19) (d:=1680) (e:=1696) (n:=16) (k:=16) (by decide) (by decide) (by decide)
  change WP isa (.seq (Paired.reject 400 a .x22 w16) (.seq (.block _) _)) s _
  apply WP.assoc
  refine WP.seq (WP.mono (initialOne_ok s (buf:=400) (slot:=1680) (flag:=.x22)
    (by decide) ha (by decide) (by decide) (by decide) pa hc
    (Noise.inScratch hs (by decide) (by decide)) (Noise.inScratch hs (by decide) (by decide))
    (da.sub_right cpA)) fun u hu => ?_)
  have u19 : u.gpr .x19=s.gpr .x19 := hu.keep.get .x19 (by decide)
  have u28 : u.gpr .x28=s.gpr .x28 := hu.keep.get .x28 (by decide)
  have u16 : u.gpr .x16=s.gpr .x16 := hu.keep.get .x16 (by decide)
  have pb' : Rej8.EnvW w16 168 B (u.gpr .x19+BitVec.ofNat 64 904) (u.gpr .x28+BitVec.ofNat 64 b) u := by
    rw [u19,u28]
    refine pb.frame hu.keep.rd hu.keep.wr u16 hu.frame ?_ ?_
    · intro r hr
      simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (da.sub_right (Offset.sub_base _ (by decide))).symm
      · exact Offset.disjoint (s.gpr .x19) (d:=904) (n:=508) (e:=1680) (k:=16) (by decide) (by decide) (by decide)
    · intro mask hm r hr
      simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact pa.tableDisj mask hm
      · exact (dt mask hm).sub_right cpA
  apply WP.assoc
  refine WP.seq (WP.mono (initialOne_ok u (buf:=904) (slot:=1696) (flag:=.x23)
    (by decide) hb (by decide) (by decide) (by decide) pb' hu.constants
    (by rw [hu.keep.wr,u19]; exact Noise.inScratch hs (by decide) (by decide))
    (by rw [hu.keep.wr,u19]; exact Noise.inScratch hs (by decide) (by decide))
    (by rw [u19,u28]; exact db.sub_right cpB)) fun v hv => ?_)
  have fv : Frame (initialWrites (s.gpr .x19+BitVec.ofNat 64 1696) (s.gpr .x28+BitVec.ofNat 64 b)) u.mem v.mem := by
    simpa only [u19,u28] using hv.frame
  have first := coeffs_frame hu.coeffs (sampleAfter_length_le (by decide) A 168) fv (by
    intro r hr; simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact dab
    · exact da.sub_right cpB)
  have saved := checkpoint_frame hu.saved fv (by
    intro r hr; simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (db.sub_right cpA).symm
    · exact cpAB)
  have flagA : (v.gpr .x22).toNat=if (sampleAfter [] A 168).length=256 then 1 else 0 := by
    rw [hv.keep.get .x22 (by decide),hu.flagValue]
  have frame : Frame (initialRegions (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a)
      (s.gpr .x28+BitVec.ofNat 64 b)) s.mem v.mem :=
    (hu.frame.mono (by simp [initialWrites,initialRegions])).trans
      (fv.mono (by simp [initialWrites,initialRegions]))
  have hand : WP isa (.block [.logic .and .x .x6 .x22 .x23]) v fun t =>
      Only [.x6] v t ∧ t.gpr .x6=(v.gpr .x22 &&& v.gpr .x23) :=
    wp_and fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.mono (WP.keepV (by rfl) hand) fun t ⟨⟨ht,et⟩,vt⟩ => ?_
  refine ⟨((hu.keep.trans hv.keep).trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem]; exact frame
  · rw [ht.mem]; exact first
  · rw [ht.mem]; simpa only [u28] using hv.coeffs
  · rw [ht.mem]; exact saved
  · rw [ht.mem]; simpa only [u19,u28] using hv.saved
  · rw [ht.get .x22 (by decide),flagA]
  · rw [ht.get .x23 (by decide),hv.flagValue]
  · rw [et,BitVec.toNat_and,flagA,hv.flagValue]
    split <;> split <;> simp_all
  · exact ⟨by rw [vt]; exact hv.constants.index,by rw [vt]; exact hv.constants.mask,
      by simpa only [vt] using hv.constants.q,by simpa only [vt] using hv.constants.weights,
      by simpa only [vt] using hv.constants.zero⟩

end VG.Proof.MlKem.AArch64.Paired
