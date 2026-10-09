import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackGroup

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
