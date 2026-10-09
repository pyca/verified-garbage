import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFallback

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorSetup vectorBody)

theorem Layout.keep {s t : State} {table p q : Addr} {X : List Byte} (h : Layout s table p q X)
    {rs : List Reg} (hk : Keep rs s t) (hm : t.mem=s.mem) : Layout t table p q X := by
  rcases h with ⟨hs,he,hx,ha,ht,hr,htr,hw⟩
  exact ⟨hs,he,by simpa only [hm] using hx,ha,ht,by simpa only [hk.rd,hk.wr] using hr,
    by simpa only [hk.rd,hk.wr] using htr,by simpa only [hk.wr] using hw⟩

theorem ScalarLayout.keep {s t : State} {p q : Addr} {X : List Byte} (h : ScalarLayout s p q X)
    {rs : List Reg} (hk : Keep rs s t) (hm : t.mem=s.mem) : ScalarLayout t p q X := by
  rcases h with ⟨hs,hx,ha,hr,hw⟩
  exact ⟨hs,by simpa only [hm] using hx,ha,by simpa only [hk.rd,hk.wr] using hr,
    by simpa only [hk.wr] using hw⟩

def parseCore (η : Nat) : Prog isa :=
 .seq (.block (scalarSetup η++vectorSetup η++
   [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]))
 (.seq (.ite (.zero .x .x8) (.block []) (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
   (fallback η))

theorem parseCore_ok {s : State} {η : Nat} (he : η=2∨η=4) {table p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hx : X.length=272)
    (hv : Layout s table p q X) (hs : ScalarLayout s p q X)
    (hT : TableAt s.mem table) (hS : Stored s.mem p L)
    (h2 : s.gpr .x2=q) (h3 : s.gpr .x3=p) (h4 : s.gpr .x4=BitVec.ofNat 64 (256-L.length))
    (ht : s.gpr .x19+6000=table) :
    WP isa (parseCore η) s fun t=>Keep (.x0::parserRegs) s t ∧ Frame [polyR p] s.mem t.mem ∧
      Stored t.mem p (rbFold η L X) ∧ (t.gpr .x4).toNat=256-(rbFold η L X).length := by
  unfold parseCore
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (scalarSetup_ok he hl h3 h4) fun a ⟨ha,haC⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (vectorSetup_ok he haC.q haC.eta haC.mask haC.bound) fun b ⟨hb,hbC⟩=>?_
  have hbT : a.gpr .x19+6000=table := by rw [ha.keep.gpr .x19 (by decide)]; exact ht
  rw [hbT] at hbC
  refine WP.mono (guard_ok hbC.four hbC.zero) fun c ⟨hc,hcv,h8⟩=>?_
  have hk := (ha.keep.trans hb.keep).trans hc.keep
  have hm : c.mem=s.mem := hc.mem.trans (hb.mem.trans ha.mem)
  have hC : Consts η table c := hbC.keep hc.keep (by decide) (fun _ _=>congrFun hcv _)
  have hr : c.gpr .x4=BitVec.ofNat 64 (256-L.length) := by
    rw [hk.gpr .x4 (by decide)]; exact h4
  have hb5 : b.gpr .x5=272 := by rw [hb.keep.gpr .x5 (by decide)]; exact haC.bytes
  have hg : c.gpr .x8=if L.length≤252 then BitVec.ofNat 64 X.length else 0 := by
    rw [h8,hb5,hb.keep.gpr .x4 (by decide),ha.keep.gpr .x4 (by decide),h4,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),hx]
    by_cases hh : L.length≤252
    · rw [ite_eq_left hh,ite_eq_left (by omega : 4≤256-L.length)]
      rfl
    · rw [ite_eq_right hh,ite_eq_right (by omega : ¬4≤256-L.length)]
  have hi : LoopInv c η table p q L X 0 c := by
    refine ⟨by omega,rfl,hC,?_,Keep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_,?_⟩
    · rw [hm]; exact hT
    · change Stored c.mem p L
      rw [hm]; exact hS
    · change c.gpr .x2=q+0#64
      rw [BitVec.add_zero]
      rw [hk.gpr .x2 (by decide)]; exact h2
    · change c.gpr .x3=coeffAddr p L.length
      rw [hc.get .x3,hb.keep.gpr .x3 (by decide)]; exact haC.output
    · exact hr
    · simp only [Nat.sub_zero,hx]
      rw [hc.get .x5]; exact hb5
    · exact hg
  refine WP.mono (parsedPhase_ok he hl (hv.keep hk hm) (hs.keep hk hm) hi) fun t ⟨htk,htf,hts,htr⟩=>?_
  refine ⟨(hk.trans htk).mono (by decide),?_,hts,htr⟩
  rw [←hm]; exact htf

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
