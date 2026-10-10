import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackFields
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackLoop
import VerifiedGarbage.Proof.Framework.CallLay

/-! ## From `UseHintPackSpec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.Spec.MlDsa

theorem fields_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    fields g m h a = Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
      ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a) := by
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn,Vector.getElem_zipWith]
  rw [value_spec hg (ha i hi)]
  have hpoly : (⟨(coeffAt m a i).toNat,ha i hi⟩ : Zq)=(polyAt m a)[i] :=
    Fin.ext (VG.Proof.MlDsa.Pack.polyAt_val ha hi).symm
  have hh := VG.Proof.MlDsa.Round.hintAt_get m h hi
  rw [VG.Proof.MlDsa.Round.getElem!_eq _ hi] at hh
  rw [hpoly,hh]

theorem packed_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    packed g m h a = simpleBitPack
      (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
        ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a)) ((q-1)/(2*g)-1) := by
  rw [packed,fields_spec hg ha]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open HighPack
open VG.Proof.MlDsa.AArch64.Round

 theorem setup_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++Impl.MlDsa.AArch64.Optimized.HighPack.packSetup)) s fun t=>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] s t ∧ Ready g t := by
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok s g) fun a ha=>?_
  refine WP.mono (packSetup_ok a) fun t ht=>?_
  obtain ⟨hk,_,h17,h18,h19,h20,h21,h22,h23⟩ := ha
  refine ⟨hk.trans ht.1,⟨⟨?_,?_,?_,?_⟩,⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩⟩,?_,?_,?_⟩
  · intro e he;rw [ht.1.vec .v17 (by decide),h17,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v18 (by decide),h18,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v19 (by decide),h19,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v20 (by decide),h20,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v21 (by decide),h21,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v22 (by decide),h22,repeatedWord_lane _ he];rfl
  · intro e _;rw [ht.1.vec .v23 (by decide),h23];simp [vword]

 theorem code_eq (g : Nat) : Impl.MlDsa.AArch64.Optimized.UseHintPack.code g=
    .seq (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++
      Impl.MlDsa.AArch64.Optimized.HighPack.packSetup++([.movz .x .x11 16 0] : List Instr)))
      (.loop (.block (groupCode g++advance g)) (.nonzero .x .x11)) := by
  simp only [Impl.MlDsa.AArch64.Optimized.UseHintPack.code,groupCode,loadFour,advance,packWidth,
    beq_iff_eq,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackCode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlKem.AArch64 (Keep)

structure CodePost (g : Nat) (s t : State) : Prop where
  keep : Keep [.x4,.x5,.x1,.x9,.x11] s t
  frame : Frame [⟨s.gpr .x1,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x1) (32*packWidth g)=
    packed g s.mem (s.gpr .x4) (s.gpr .x5)

/-- Complete correctness of the exact selected packing function, including
setup, fixed-count loop, output frame, and callee-saved registers. -/
theorem code_ok {g : Nat} (hg : IsG g) (s : State)
    (hr : Reduced s.mem (s.gpr .x5))
    (hsep : (polyRegion (s.gpr .x5)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩)
    (hbsep : (polyRegion (s.gpr .x4)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩)
    (hhin : ∀j<16,∀k<4,InRegions (s.rd++s.wr)
      ((s.gpr .x4+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ j<16, ∀ k<4, InRegions (s.rd++s.wr)
      ((s.gpr .x5+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s.wr
      ((s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (Impl.MlDsa.AArch64.Optimized.UseHintPack.code g) s (CodePost g s) := by
  rw [code_eq]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (setup_ready s hg) fun a ha => ?_
  let u := a.write .x .x11 16
  refine WP.block_cons_iff.mpr ⟨u,rfl,WP.block_nil_iff.mpr ?_⟩
  have um : u.mem=s.mem := ha.1.mem
  have ur : u.rd=s.rd := ha.1.rd
  have uw : u.wr=s.wr := ha.1.wr
  have up : u.sp=s.sp := ha.1.sp
  have ug (r : Reg) (h9 : r≠.x9) (h11 : r≠.x11) : u.gpr r=s.gpr r := by
    change (if r=.x11 then 16 else a.gpr r)=s.gpr r
    rw [ite_eq_right h11,ha.1.gpr r h9]
  have initial : LoopState u (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) g 0 u := by
    refine ⟨by decide,ha.2.sameVectors rfl,?_,Frame.refl _ _,?_,?_,?_,rfl,
      fun _ _ _ _ _ _ => rfl,fun _ _ => rfl,rfl,rfl,rfl⟩
    · intro i hi; omega
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x4 (by decide) (by decide)
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x5 (by decide) (by decide)
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x1 (by decide) (by decide)
  refine WP.mono (loop_ok hg (by decide) initial (by rw [um]; exact hr) hsep hbsep
    (fun j hj k hk=>by rw [ur,uw];exact hhin j hj k hk)
    (fun j hj k hk => by rw [ur,uw]; exact hin j hj k hk)
    (fun j hj => by rw [uw]; exact hw8 j hj)
    (fun j hj hw => by rw [uw]; exact hw4 j hj hw)) fun t ht => ?_
  refine ⟨?_,?_,?_⟩
  · refine ⟨?_,ht.rd.trans ur,ht.wr.trans uw,ht.sp.trans up,?_⟩
    · intro r hn
      have hh : r≠.x4 ∧ r≠.x5 ∧ r≠.x1 ∧ r≠.x9 ∧ r≠.x11 := by simpa using hn
      rw [ht.gpr r hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2,ug r hh.2.2.2.1 hh.2.2.2.2]
    · intro r hr
      have htemp : r∉temps := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hc : r∉[VReg.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ht.vec r htemp]
      change (a.v r).extractLsb' 0 64=(s.v r).extractLsb' 0 64
      rw [ha.1.vec r hc]
  · simpa only [um] using ht.frame
  · simpa only [um] using ht.output_bytes hg

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackProg.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)
open VG.Proof.MlKem.AArch64 (Keep)

structure Pre (g : Nat) (s : State) : Prop where
  gamma : arg32 s .x3=g
  reduced : Reduced s.mem (s.gpr .x2)
  input : InRegions (s.rd++s.wr) (s.gpr .x2) 1024
  hints : InRegions (s.rd++s.wr) (s.gpr .x1) 1024
  output : InRegions s.wr (s.gpr .x0) (32*packWidth g)
  sep : (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩
  hintSep : (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩

structure Post (g : Nat) (s t : State) : Prop where
  frame : Frame [⟨s.gpr .x0,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)

private theorem subregion {rs : List Region} {p : Addr} {len off n : Nat}
    (h : InRegions rs p len) (hb : off+n≤len) (ho : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) n := by
  obtain ⟨r,hr,hp⟩ := h
  exact ⟨r,hr,VG.CallLay.contains_trans hp hb ho⟩

/-- Dispatch accepts the ABI's 32-bit gamma argument; its upper register bits are irrelevant. -/
theorem prog_ok {g : Nat} (hg : IsG g) {s : State} (hp : Pre g s) :
    WP isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s (Post g s) := by
  unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
  apply WP.seq
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x4,.x5,.x1]
    (Q:=fun a=>a.gpr .x4=s.gpr .x1 ∧ a.gpr .x5=s.gpr .x2 ∧
      a.gpr .x1=s.gpr .x0 ∧ a.mem=s.mem)
    (by arun) (by decide +kernel) (hv:=rfl)) fun a ha=>?_
  apply zext_ok
  apply onGamma_ok (by decide : Reg.x6≠.x3)
  · rw [zextS_toNat]
    have hh : arg32 a .x3=g := by
      unfold arg32; rw [ha.2.get .x3 (by decide)]; exact hp.gamma
    rw [hh]; exact hg
  · intro g' he b hk hm
    have hsame : g'=g := by
      rw [zextS_toNat] at he
      unfold arg32 at he
      rw [ha.2.get .x3 (by decide)] at he
      exact he.symm.trans hp.gamma
    rw [hsame]
    have bm : b.mem=s.mem := hm.trans ha.1.2.2.2
    have br : b.rd=s.rd := hk.rd.trans ha.2.rd
    have bw : b.wr=s.wr := hk.wr.trans ha.2.wr
    have bh : b.gpr .x4=s.gpr .x1 := by
      rw [hk.get .x4 (by decide),zextS_other _ (by decide)]; exact ha.1.1
    have bi : b.gpr .x5=s.gpr .x2 := by
      rw [hk.get .x5 (by decide),zextS_other _ (by decide)]; exact ha.1.2.1
    have bo : b.gpr .x1=s.gpr .x0 := by
      rw [hk.get .x1 (by decide),zextS_other _ (by decide)]; exact ha.1.2.2.1
    refine WP.mono (code_ok hg b (by rw [bm,bi];exact hp.reduced)
      (by rw [bi,bo];exact hp.sep) (by rw [bh,bo];exact hp.hintSep) ?_ ?_ ?_ ?_) fun t ht=>?_
    · intro j hj k hk
      rw [br,bw,bh,Offset.add_add]
      exact subregion hp.hints (by omega) (by omega)
    · intro j hj k hk
      rw [br,bw,bi,Offset.add_add]
      exact subregion hp.input (by omega) (by omega)
    · intro j hj
      rw [bw,bo]
      apply subregion hp.output
      · rcases hg with rfl|rfl
        · change 8*j+8≤128;omega
        · change 12*j+8≤192;omega
      · rcases hg with rfl|rfl <;> decide
    · intro j hj hw
      rw [bw,bo]
      change InRegions s.wr ((s.gpr .x0+BitVec.ofNat 64 (2*packWidth g*j))+BitVec.ofNat 64 8) 4
      rw [Offset.add_add]
      apply subregion hp.output
      · rw [hw];omega
      · rw [hw];omega
    · exact ⟨by simpa only [bm,bo] using ht.frame,
        by simpa only [bm,bo,bh,bi] using ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end
