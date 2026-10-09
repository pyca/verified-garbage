import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem parse_ok {s : State} {η k off : Nat} (he : η=2∨η=4) (hk : k<4) (ho : off≤272)
    {table p q a : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256) (hx : X.length=272)
    (hv : Layout s table p q X) (hs : ScalarLayout s p q X)
    (hT : TableAt s.mem table) (hS : Stored s.mem p L)
    (hq : s.gpr .x19+BitVec.ofNat 64 (840+544*k+off)=q)
    (hp : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p)
    (ha : s.gpr .x19+BitVec.ofNat 64 (7904+8*k)=a)
    (ht : s.gpr .x19+6000=table)
    (hc : s.mem.readW a 64=BitVec.ofNat 64 (256-L.length))
    (hr : InRegions (s.rd++s.wr) a 8) (hw : InRegions s.wr a 8)
    (hsep : (polyR p).Disjoint ⟨a,8⟩) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) s fun t=>
      Keep (.x0::parserRegs) s t ∧ Frame [polyR p,⟨a,8⟩] s.mem t.mem ∧
      Stored t.mem p (rbFold η L X) ∧
      t.mem.readW a 64=BitVec.ofNat 64 (256-(rbFold η L X).length) := by
  rw [parse_wp]
  refine WP.seq (WP.mono (parseAddress_ok hk ho (by rw [ha]; exact hr)) fun u ⟨hu,h2,h3,h4⟩=>?_)
  rw [hq] at h2
  rw [hp] at h3
  rw [ha,hc] at h4
  refine WP.seq (WP.mono (parseCore_ok he hl hx (hv.keep hu.keep hu.mem)
    (hs.keep hu.keep hu.mem) (by rw [hu.mem]; exact hT)
    (by rw [hu.mem]; exact hS) h2 h3 h4
    (by rw [hu.get .x19]; exact ht)) fun v ⟨hvK,hvF,hvS,hvC⟩=>?_)
  have hvA : v.gpr .x19+BitVec.ofNat 64 (7904+8*k)=a := by
    rw [hvK.gpr .x19 (by decide),hu.get .x19]; exact ha
  refine wp_strx (by omega) hvA (by rw [hvK.wr,hu.wr]; exact hw) fun t htw=>wp_nil ?_
  have hf : Frame [⟨a,8⟩] v.mem t.mem := by
    rw [htw.mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self a 8)
  refine ⟨((hu.keep.trans hvK).trans htw.keep).mono (by decide),?_,?_,?_⟩
  · have hfull : Frame [polyR p,⟨a,8⟩] u.mem t.mem := (hvF.mono (fun r hr=>by simp only [List.mem_singleton] at hr; simp [hr])).trans
      (hf.mono (fun r hr=>by simp only [List.mem_singleton] at hr; simp [hr]))
    rw [hu.mem] at hfull
    exact hfull
  · exact stored_frame hf (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hsep)
      hvS (rbFold_length_le hl _)
  · rw [htw.mem,Mem.readW_writeW_self64]
    rw [←hvC]
    simp

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
