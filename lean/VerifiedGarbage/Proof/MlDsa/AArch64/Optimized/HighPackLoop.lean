module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackBlock
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `MlDsa.AArch64.Optimized.HighPackBody`, which only this module used -/

section

/-! ## From `HighPackGroup.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

def groupTemps : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7]

def groupCode (g : Nat) : List Instr :=
  (([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) =>
    [.ldrq r .x0 (16*j)] ++ hb g r r) ++ packTail (packWidth g)

structure GroupPost (g block : Nat) (a : Addr) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀ r, r∉groupTemps → t.v r=s.v r
  ready : PackReady g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (highPacked g (polyAt s.mem a))[(2*packWidth g)*block+i]!

/-- One actual machine group reads sixteen coefficients, computes HighBits,
and writes the corresponding original-specification bytes. -/
theorem group_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {a : Addr} {s : State} (hr : Reduced s.mem a) (hc : PackReady g s)
    (hp : s.gpr .x0=a+BitVec.ofNat 64 (64*block))
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GroupPost g block a s t → WP isa (.block rest) t Q) :
    WP isa (.block (groupCode g ++ rest)) s Q := by
  unfold groupCode
  rw [List.append_assoc]
  refine loadFour_ok hg hc.toHighConstants hin fun u hu _ hv => ?_
  have cu := hc.afterLoads hu
  refine packTail_ok hg cu (by rw [hu.wr,hu.gpr]; exact hw8)
    (fun h => by rw [hu.wr,hu.gpr]; exact hw4 h) fun t ht => ?_
  refine k t ⟨(hu.keep.trans ht.keep).mono (by decide),?_,ht.ready,?_,?_⟩
  · intro r hrt
    have h0 : r∉[VReg.v0,.v1,.v2,.v3,.v7] := by
      intro h; exact hrt (by simp only [groupTemps,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    have h1 : r∉[VReg.v4,.v5,.v6] := by
      intro h; exact hrt (by simp only [groupTemps,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    rw [ht.vec r h1,hu.get r h0]
  · simpa only [hu.gpr,hu.mem] using ht.frame
  · intro i hi
    have hbyte := ht.bytes i hi
    rw [hu.gpr] at hbyte
    rw [hbyte]
    exact packedVector_spec hg hr cu.toPackConstants hb hi (by simpa only [hp] using hv)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

/-! ## From `HighPackBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

def advance (g : Nat) : List Instr :=
  [.addImm .x .x0 .x0 64,.addImm .x .x1 .x1 (2*packWidth g),.subImm .x .x11 .x11 1]

theorem advance_ok (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (advance g)) s fun t =>
      t.gpr .x0=s.gpr .x0+64 ∧
      t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g) ∧ t.gpr .x11=s.gpr .x11-1 ∧
      (∀ r, r≠.x0 → r≠.x1 → r≠.x11 → t.gpr r=s.gpr r) ∧
      t.v=s.v ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  let a := s.write .x .x0 (s.gpr .x0+64)
  let b := a.write .x .x1 (a.gpr .x1+BitVec.ofNat 64 (2*packWidth g))
  let t := b.write .x .x11 (b.gpr .x11-1)
  refine WP.block_cons_iff.mpr ⟨a,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨b,?_,?_⟩
  · have hw : 2*packWidth g<4096 := by rcases hg with rfl | rfl <;> decide
    simp [isa,exec,hw,State.read,b]
  refine WP.block_cons_iff.mpr ⟨t,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [t,b,a]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [show Reg.x0≠.x11 by decide,show Reg.x0≠.x1 by decide,
    show Reg.x1≠.x11 by decide,show Reg.x1≠.x0 by decide,
    show Reg.x11≠.x1 by decide,show Reg.x11≠.x0 by decide,ite_false,ite_true,true_and]
  constructor
  · intro r h0 h1 h11
    simp only [h0,h1,h11,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem PackReady.sameVectors {g : Nat} {s t : State} (h : PackReady g s) (hv : t.v=s.v) :
    PackReady g t := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
  · rw [hv]; exact h.add
  · rw [hv]; exact h.mul
  · rw [hv]; exact h.round
  · rw [hv]; exact h.modulus
  · rw [hv]; exact h.zero
  · rw [hv]; exact h.idx29
  · rw [hv]; exact h.idx24
  · rw [hv]; exact h.idx25

structure BodyPost (g block : Nat) (a : Addr) (s t : State) : Prop where
  ready : PackReady g t
  input : t.gpr .x0=s.gpr .x0+64
  output : t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g)
  count : t.gpr .x11=s.gpr .x11-1
  gpr : ∀ r, r≠.x0 → r≠.x1 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ r, r∉groupTemps → t.v r=s.v r
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (highPacked g (polyAt s.mem a))[(2*packWidth g)*block+i]!
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Complete loop body, including exact pointer and public counter updates. -/
theorem body_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {a : Addr} {s : State} (hr : Reduced s.mem a) (hc : PackReady g s)
    (hp : s.gpr .x0=a+BitVec.ofNat 64 (64*block))
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (BodyPost g block a s) := by
  refine group_ok hg hb hr hc hp hin hw8 hw4 fun u hu => ?_
  refine WP.mono (advance_ok u hg) fun t ht => ?_
  refine ⟨hu.ready.sameVectors ht.2.2.2.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.1,hu.keep.get .x0]
  · rw [ht.2.1,hu.keep.get .x1]
  · rw [ht.2.2.1,hu.keep.get .x11]
  · intro r h0 h1 h9 h11
    rw [ht.2.2.2.1 r h0 h1 h11,hu.keep.get r (by simpa using h9)]
  · intro r hr
    rw [ht.2.2.2.2.1,hu.vec r hr]
  · rw [ht.2.2.2.2.2.1]; exact hu.frame
  · intro i hi
    rw [ht.2.2.2.2.2.1]; exact hu.bytes i hi
  · exact ht.2.2.2.2.2.2.1.trans hu.keep.rd
  · exact ht.2.2.2.2.2.2.2.1.trans hu.keep.wr
  · exact ht.2.2.2.2.2.2.2.2.trans hu.keep.sp

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

end

end


@[expose] public section

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
    · change 8*j+8≤128; omega_using [hj]
    · change 12*j+12≤192; omega_using [hj]
  have small : 32*packWidth g<2^64 := by rcases hg with rfl | rfl <;> decide
  refine ⟨by omega_using [hj],ht.ready,?_,?_,?_,?_,?_,?_,?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩
  · intro i hi
    rw [Nat.mul_succ] at hi
    by_cases old : i<(2*packWidth g)*j
    · rw [hf.bytes (R := ⟨o,(2*packWidth g)*j⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simpa only [BitVec.add_zero] using
          (Offset.disjoint o (d := 0) (n := (2*packWidth g)*j)
            (e := (2*packWidth g)*j) (k := 2*packWidth g)
            (Or.inl (by omega_using [])) (by omega_using [full, small]) (by omega_using [full, small]))) (by dsimp; omega_using [full, small]) old]
      exact h.values i old
    · have hb := ht.bytes (i-(2*packWidth g)*j) (by omega_using [full, hi])
      rw [h.output,Offset.add_add,show (2*packWidth g)*j+(i-(2*packWidth g)*j)=i by omega_using [old],poly] at hb
      exact hb
  · exact h.frame.trans (hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨⟨o,32*packWidth g⟩,by simp,Offset.sub_base o full⟩))
  · rw [ht.input,h.input]
    change (a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=a+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.output,h.output,Offset.add_add,Nat.mul_succ]
  · rw [ht.count,h.count]; bv_omega_arith
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
    refine ⟨?_,16-(j+1),by omega_using [hj, hl],j+1,by omega_using [hj, hend],rfl,hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,Option.some.injEq,bne_iff_ne]
    bv_omega_arith


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
    have he : 2*packWidth g*16=32*packWidth g := by omega_using []
    omega_using [hh]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
