import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackInit

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
