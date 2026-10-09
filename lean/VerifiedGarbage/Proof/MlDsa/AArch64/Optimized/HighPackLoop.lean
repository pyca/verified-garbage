import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackBody
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)

structure LoopState (s₀ : State) (a o : Addr) (g j : Nat) (s : State) : Prop where
  bound : j≤16
  ready : PackReady g s
  values : ∀ i<(2*packWidth g)*j, s.mem (o+BitVec.ofNat 64 i)=(highPacked g (polyAt s₀.mem a))[i]!
  frame : Frame [⟨o,32*packWidth g⟩] s₀.mem s.mem
  input : s.gpr .x0=a+BitVec.ofNat 64 (64*j)
  output : s.gpr .x1=o+BitVec.ofNat 64 ((2*packWidth g)*j)
  count : s.gpr .x11=BitVec.ofNat 64 (16-j)
  gpr : ∀ r, r≠.x0 → r≠.x1 → r≠.x9 → r≠.x11 → s.gpr r=s₀.gpr r
  vec : ∀ r, r∉groupTemps → s.v r=s₀.v r
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp

theorem loop_step_ok {s₀ s : State} {a o : Addr} {g j : Nat}
    (hg : IsG g) (hj : j<16) (h : LoopState s₀ a o g j s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hin : ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (LoopState s₀ a o g (j+1)) := by
  have sep : ∀ r∈[Region.mk o (32*packWidth g)], (polyRegion a).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hsep
  have red := VG.Proof.MlDsa.Arith.reduced_frame h.frame sep hr
  have poly := VG.Proof.MlDsa.Arith.polyAt_frame h.frame sep
  refine WP.mono (body_ok hg hj red h.ready h.input
    (fun k hk => by simpa only [h.rd,h.wr,h.input] using hin k hk)
    (by simpa only [h.wr,h.output] using hw8)
    (fun hw => by simpa only [h.wr,h.output] using hw4 hw)) ?_
  intro t ht
  have hf : Frame [⟨o+BitVec.ofNat 64 ((2*packWidth g)*j),2*packWidth g⟩] s.mem t.mem := by
    simpa only [h.output] using ht.frame
  have full : (2*packWidth g)*j+2*packWidth g≤32*packWidth g := by
    rcases hg with rfl | rfl
    · change 8*j+8≤128; omega
    · change 12*j+12≤192; omega
  have small : 32*packWidth g<2^64 := by rcases hg with rfl | rfl <;> decide
  refine ⟨by omega,ht.ready,?_,?_,?_,?_,?_,?_,?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩
  · intro i hi
    rw [Nat.mul_succ] at hi
    by_cases old : i<(2*packWidth g)*j
    · rw [hf.bytes (R := ⟨o,(2*packWidth g)*j⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simpa only [BitVec.add_zero] using
          (Offset.disjoint o (d := 0) (n := (2*packWidth g)*j)
            (e := (2*packWidth g)*j) (k := 2*packWidth g)
            (Or.inl (by omega)) (by omega) (by omega))) (by dsimp; omega) old]
      exact h.values i old
    · have hb := ht.bytes (i-(2*packWidth g)*j) (by omega)
      rw [h.output,Offset.add_add,show (2*packWidth g)*j+(i-(2*packWidth g)*j)=i by omega,poly] at hb
      exact hb
  · exact h.frame.trans (hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨⟨o,32*packWidth g⟩,by simp,Offset.sub_base o full⟩))
  · rw [ht.input,h.input]
    change (a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=a+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.output,h.output,Offset.add_add,Nat.mul_succ]
  · rw [ht.count,h.count]; bv_omega
  · intro r h0 h1 h9 h11
    exact (ht.gpr r h0 h1 h9 h11).trans (h.gpr r h0 h1 h9 h11)
  · intro r hv
    exact (ht.vec r hv).trans (h.vec r hv)


/-- The exact loop executes sixteen groups and establishes the complete
encoded output while preserving the original input polynomial. -/
theorem loop_ok {s₀ s : State} {a o : Addr} {g start : Nat}
    (hg : IsG g) (hstart : start<16) (h : LoopState s₀ a o g start s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hin : ∀ j<16, ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.loop (.block (groupCode g ++ advance g)) (.nonzero .x .x11)) s
      (LoopState s₀ a o g 16) := by
  let I : Nat → State → Prop := fun left t => ∃ j, j<16 ∧ left=16-j ∧ LoopState s₀ a o g j t
  refine WP.loop (M := isa) I (fun left t ⟨j,hj,hl,ht⟩ => ?_) (16-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (loop_step_ok hg hj ht hr hsep (hin j hj) (hw8 j hj) (hw4 j hj)) ?_
  intro u hu
  by_cases hend : j+1=16
  · left
    refine ⟨?_,hend ▸ hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,hend,Nat.sub_self]
    rfl
  · right
    refine ⟨?_,16-(j+1),by omega,j+1,by omega,rfl,hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,Option.some.injEq,bne_iff_ne]
    bv_omega


/-- The proved setup and loop are precisely the selected emitted function. -/
theorem code_eq (g : Nat) : VG.Impl.MlDsa.AArch64.Optimized.HighPack.code g =
    .seq (.block (VG.Impl.MlDsa.AArch64.Optimized.HighPack.constants g ++
      VG.Impl.MlDsa.AArch64.Optimized.HighPack.packSetup ++ ([.movz .x .x11 16 0] : List Instr)))
      (.loop (.block (groupCode g ++ advance g)) (.nonzero .x .x11)) := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.HighPack.code,groupCode,advance,packWidth,
    beq_iff_eq,List.append_assoc]

/-- At loop completion, the complete output buffer is the original encoding. -/
theorem LoopState.output_bytes {s₀ s : State} {a o : Addr} {g : Nat}
    (hg : IsG g) (h : LoopState s₀ a o g 16 s) :
    VG.Spec.Sha3.bytesAt s.mem o (32*packWidth g)=highPacked g (polyAt s₀.mem a) := by
  apply List.ext_getElem
  · simp only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range,highPacked_length hg]
  · intro i hi hj
    simp only [VG.Spec.Sha3.bytesAt,List.getElem_map,List.getElem_range]
    rw [←getElem!_pos (highPacked g (polyAt s₀.mem a)) i hj]
    apply h.values
    have hh : i<32*packWidth g := by
      simpa only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range] using hi
    have he : 2*packWidth g*16=32*packWidth g := by omega
    omega

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
