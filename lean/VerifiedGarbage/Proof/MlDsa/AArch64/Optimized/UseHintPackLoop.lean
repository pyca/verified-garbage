import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackFields
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-! ## From `UseHintPackFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg)

def temps : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v26]

 theorem Ready.chg {g : Nat} {s t : State} (h : Ready g s) {rs : List VReg}
    (k : VChg rs s t) (hrs : rs⊆temps) : Ready g t := by
  have hk := k.mono hrs
  refine ⟨⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩,?_,?_,?_⟩
  · intro e he; rw [hk.get .v17 (by decide)]; exact h.add e he
  · intro e he; rw [hk.get .v18 (by decide)]; exact h.mul e he
  · intro e he; rw [hk.get .v19 (by decide)]; exact h.round e he
  · intro e he; rw [hk.get .v20 (by decide)]; exact h.modulus e he
  · rw [hk.get .v28 (by decide)]; exact h.zero
  · rw [hk.get .v29 (by decide)]; exact h.idx29
  · rw [hk.get .v24 (by decide)]; exact h.idx24
  · rw [hk.get .v25 (by decide)]; exact h.idx25
  · intro e he; rw [hk.get .v21 (by decide)]; exact h.factor e he
  · intro e he; rw [hk.get .v22 (by decide)]; exact h.one e he
  · intro e he; rw [hk.get .v23 (by decide)]; exact h.z e he

 def loadFour (g : Nat) : List Instr :=
  ([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j)=>
    Impl.MlDsa.AArch64.Optimized.UseHintPack.four g r (16*j)

 theorem loadFour_ok {g : Nat} (hg : IsG g) {s : State} (hc : Ready g s)
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg temps s t → Ready g t →
      (∀j<4,∀e<4,vword (t.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=value g
        (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16) e)
        (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (loadFour g++rest)) s Q := by
  change WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v0 0 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v1 16 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v2 32 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v3 48 ++ rest))))) s Q
  refine four_ok hg (by decide) hc (by decide) (ha 0 (by decide)) (hh 0 (by decide)) fun a h0 w0=>?_
  have c0 := hc.chg h0 (by decide)
  refine four_ok hg (by decide) c0 (by decide)
    (by rw [h0.rd,h0.wr,h0.gpr]; exact ha 1 (by decide))
    (by rw [h0.rd,h0.wr,h0.gpr]; exact hh 1 (by decide)) fun b h1 w1=>?_
  have k1 := h0.trans h1
  have c1 := c0.chg h1 (by decide)
  refine four_ok hg (by decide) c1 (by decide)
    (by rw [k1.rd,k1.wr,k1.gpr]; exact ha 2 (by decide))
    (by rw [k1.rd,k1.wr,k1.gpr]; exact hh 2 (by decide)) fun c h2 w2=>?_
  have k2 := k1.trans h2
  have c2 := c1.chg h2 (by decide)
  refine four_ok hg (by decide) c2 (by decide)
    (by rw [k2.rd,k2.wr,k2.gpr]; exact ha 3 (by decide))
    (by rw [k2.rd,k2.wr,k2.gpr]; exact hh 3 (by decide)) fun t h3 w3=>?_
  refine k t ((k2.trans h3).mono (by decide)) (c2.chg h3 (by decide)) ?_
  intro j hj e he
  rcases (show j=0∨j=1∨j=2∨j=3 by omega) with rfl|rfl|rfl|rfl
  · change vword (t.v .v0) e=_
    rw [h3.get .v0 (by decide),h2.get .v0 (by decide),h1.get .v0 (by decide),w0 e he]
  · change vword (t.v .v1) e=_
    rw [h3.get .v1 (by decide),h2.get .v1 (by decide),w1 e he,h0.mem,h0.gpr]
  · change vword (t.v .v2) e=_
    rw [h3.get .v2 (by decide),w2 e he,k1.mem,k1.gpr]
  · change vword (t.v .v3) e=_
    rw [w3 e he,k2.mem,k2.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep VChg)
open HighPack (packWidth)

def groupCode (g : Nat) : List Instr :=
  loadFour g++Impl.MlDsa.AArch64.Optimized.HighPack.packTail (packWidth g)

structure GroupPost (g block : Nat) (h a : Addr) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀r,r∉temps→t.v r=s.v r
  ready : Ready g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀i<2*packWidth g,t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (packed g s.mem h a)[2*packWidth g*block+i]!

 theorem group_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {h a : Addr} {s : State} (hr : Reduced s.mem a) (hc : Ready g s)
    (hp : s.gpr .x5=a+BitVec.ofNat 64 (64*block))
    (hhp : s.gpr .x4=h+BitVec.ofNat 64 (64*block))
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6→InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,GroupPost g block h a s t→WP isa (.block rest) t Q) :
    WP isa (.block (groupCode g++rest)) s Q := by
  unfold groupCode
  rw [List.append_assoc]
  refine loadFour_ok hg hc ha hh fun u hu cu hv=>?_
  refine HighPack.packTail_ok hg cu.toPackReady (by rw [hu.wr,hu.gpr];exact hw8)
    (fun h=>by rw [hu.wr,hu.gpr];exact hw4 h) fun t ht=>?_
  refine k t ⟨(hu.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r hr
    rw [ht.vec r (by intro h;exact hr (by simp only [temps,List.mem_cons,List.not_mem_nil,or_false] at *;grind only)),hu.get r hr]
  · refine ⟨ht.ready,?_,?_,?_⟩
    · intro e he;rw [ht.vec .v21 (by decide)];exact cu.factor e he
    · intro e he;rw [ht.vec .v22 (by decide)];exact cu.one e he
    · intro e he;rw [ht.vec .v23 (by decide)];exact cu.z e he
  · simpa only [hu.gpr,hu.mem] using ht.frame
  · intro i hi
    have hx:=ht.bytes i hi
    rw [hu.gpr] at hx
    rw [hx]
    exact packed_fields_byte hg hr cu.toPackConstants hb hi (by simpa only [hp,hhp] using hv)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)

def advance (g : Nat) : List Instr :=
  [.addImm .x .x4 .x4 64,.addImm .x .x5 .x5 64,.addImm .x .x1 .x1 (2*packWidth g),.subImm .x .x11 .x11 1]

theorem advance_ok (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (advance g)) s fun t =>
      t.gpr .x4=s.gpr .x4+64 ∧ t.gpr .x5=s.gpr .x5+64 ∧
      t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g) ∧ t.gpr .x11=s.gpr .x11-1 ∧
      (∀r,r≠.x4→r≠.x5→r≠.x1→r≠.x11→t.gpr r=s.gpr r) ∧
      t.v=s.v ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  let a := s.write .x .x4 (s.gpr .x4+64)
  let b := a.write .x .x5 (a.gpr .x5+64)
  let c := b.write .x .x1 (b.gpr .x1+BitVec.ofNat 64 (2*packWidth g))
  let t := c.write .x .x11 (c.gpr .x11-1)
  refine WP.block_cons_iff.mpr ⟨a,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨b,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨c,?_,?_⟩
  · have hw : 2*packWidth g<4096 := by rcases hg with rfl|rfl <;> decide
    simp [isa,exec,hw,State.read,c]
  refine WP.block_cons_iff.mpr ⟨t,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [t,c,b,a]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [show Reg.x4≠.x11 by decide,show Reg.x4≠.x1 by decide,show Reg.x4≠.x5 by decide,
    show Reg.x5≠.x11 by decide,show Reg.x5≠.x1 by decide,show Reg.x5≠.x4 by decide,
    show Reg.x1≠.x11 by decide,show Reg.x1≠.x5 by decide,show Reg.x1≠.x4 by decide,
    show Reg.x11≠.x1 by decide,show Reg.x11≠.x5 by decide,show Reg.x11≠.x4 by decide,ite_false,ite_true,true_and]
  constructor
  · intro r h4 h5 h1 h11;simp only [h4,h5,h1,h11,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem Ready.sameVectors {g : Nat} {s t : State} (h : Ready g s) (hv : t.v=s.v) :
    Ready g t := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩,?_,?_,?_⟩
  · rw [hv]; exact h.add
  · rw [hv]; exact h.mul
  · rw [hv]; exact h.round
  · rw [hv]; exact h.modulus
  · rw [hv]; exact h.zero
  · rw [hv]; exact h.idx29
  · rw [hv]; exact h.idx24
  · rw [hv]; exact h.idx25
  · intro e he;rw [hv];exact h.factor e he
  · intro e he;rw [hv];exact h.one e he
  · intro e he;rw [hv];exact h.z e he

structure BodyPost (g block : Nat) (b a : Addr) (s t : State) : Prop where
  ready : Ready g t
  hints : t.gpr .x4=s.gpr .x4+64
  input : t.gpr .x5=s.gpr .x5+64
  output : t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g)
  count : t.gpr .x11=s.gpr .x11-1
  gpr : ∀ r, r≠.x4 → r≠.x5 → r≠.x1 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ r, r∉temps → t.v r=s.v r
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (packed g s.mem b a)[(2*packWidth g)*block+i]!
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Complete loop body, including exact pointer and public counter updates. -/
theorem body_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {b a : Addr} {s : State} (hr : Reduced s.mem a) (hc : Ready g s)
    (hp : s.gpr .x5=a+BitVec.ofNat 64 (64*block))
    (hbptr : s.gpr .x4=b+BitVec.ofNat 64 (64*block))
    (hhin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (BodyPost g block b a s) := by
  refine group_ok hg hb hr hc hp hbptr hin hhin hw8 hw4 fun u hu => ?_
  refine WP.mono (advance_ok u hg) fun t ht => ?_
  refine ⟨hu.ready.sameVectors ht.2.2.2.2.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.1,hu.keep.get .x4]
  · rw [ht.2.1,hu.keep.get .x5]
  · rw [ht.2.2.1,hu.keep.get .x1]
  · rw [ht.2.2.2.1,hu.keep.get .x11]
  · intro r h4 h0 h1 h9 h11
    rw [ht.2.2.2.2.1 r h4 h0 h1 h11,hu.keep.get r (by simpa using h9)]
  · intro r hr
    rw [ht.2.2.2.2.2.1,hu.vec r hr]
  · rw [ht.2.2.2.2.2.2.1]; exact hu.frame
  · intro i hi
    rw [ht.2.2.2.2.2.2.1]; exact hu.bytes i hi
  · exact ht.2.2.2.2.2.2.2.1.trans hu.keep.rd
  · exact ht.2.2.2.2.2.2.2.2.1.trans hu.keep.wr
  · exact ht.2.2.2.2.2.2.2.2.2.trans hu.keep.sp

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)

 theorem packed_frame {g : Nat} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {b a : Addr}
    (hb : ∀r∈rs,(polyRegion b).Disjoint r) (ha : ∀r∈rs,(polyRegion a).Disjoint r) :
    packed g m' b a=packed g m b a := by
  unfold packed
  apply congrArg (fun L=>simpleBitPack L ((q-1)/(2*g)-1))
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn]
  rw [VG.Proof.MlDsa.Arith.coeffAt_frame hf ha hi,VG.Proof.MlDsa.Arith.coeffAt_frame hf hb hi]

 theorem packed_length {g : Nat} (hg : Round.IsG g) (m : Mem) (b a : Addr) :
    (packed g m b a).length=32*packWidth g := by
  have hw : bitlen ((q-1)/(2*g)-1)=packWidth g := by rcases hg with rfl|rfl <;> rfl
  rw [packed,VG.Proof.MlDsa.Pack.simpleBitPack_eq,hw]
  exact VG.Proof.MlDsa.Pack.pack_length _ _ (by simp)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)

structure LoopState (s₀ : State) (b a o : Addr) (g j : Nat) (s : State) : Prop where
  bound : j≤16
  ready : Ready g s
  values : ∀ i<(2*packWidth g)*j, s.mem (o+BitVec.ofNat 64 i)=(packed g s₀.mem b a)[i]!
  frame : Frame [⟨o,32*packWidth g⟩] s₀.mem s.mem
  hints : s.gpr .x4=b+BitVec.ofNat 64 (64*j)
  input : s.gpr .x5=a+BitVec.ofNat 64 (64*j)
  output : s.gpr .x1=o+BitVec.ofNat 64 ((2*packWidth g)*j)
  count : s.gpr .x11=BitVec.ofNat 64 (16-j)
  gpr : ∀ r, r≠.x4 → r≠.x5 → r≠.x1 → r≠.x9 → r≠.x11 → s.gpr r=s₀.gpr r
  vec : ∀ r, r∉temps → s.v r=s₀.v r
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp

theorem loop_step_ok {s₀ s : State} {b a o : Addr} {g j : Nat}
    (hg : IsG g) (hj : j<16) (h : LoopState s₀ b a o g j s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hbsep : (polyRegion b).Disjoint ⟨o,32*packWidth g⟩)
    (hhin : ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (LoopState s₀ b a o g (j+1)) := by
  have sep : ∀ r∈[Region.mk o (32*packWidth g)], (polyRegion a).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hsep
  have red := VG.Proof.MlDsa.Arith.reduced_frame h.frame sep hr
  have bsep : ∀r∈[Region.mk o (32*packWidth g)],(polyRegion b).Disjoint r := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hbsep
  have poly := packed_frame (g:=g) h.frame bsep sep
  refine WP.mono (body_ok hg hj red h.ready h.input h.hints
    (fun k hk=>by simpa only [h.rd,h.wr,h.hints] using hhin k hk)
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
  refine ⟨by omega,ht.ready,?_,?_,?_,?_,?_,?_,?_,?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩
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
  · rw [ht.hints,h.hints]
    change (b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=b+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.input,h.input]
    change (a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=a+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.output,h.output,Offset.add_add,Nat.mul_succ]
  · rw [ht.count,h.count]; bv_omega
  · intro r h4 h0 h1 h9 h11
    exact (ht.gpr r h4 h0 h1 h9 h11).trans (h.gpr r h4 h0 h1 h9 h11)
  · intro r hv
    exact (ht.vec r hv).trans (h.vec r hv)


/-- The exact loop executes sixteen groups and establishes the complete
encoded output while preserving the original input polynomial. -/
theorem loop_ok {s₀ s : State} {b a o : Addr} {g start : Nat}
    (hg : IsG g) (hstart : start<16) (h : LoopState s₀ b a o g start s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hbsep : (polyRegion b).Disjoint ⟨o,32*packWidth g⟩)
    (hhin : ∀ j<16,∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ j<16, ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.loop (.block (groupCode g ++ advance g)) (.nonzero .x .x11)) s
      (LoopState s₀ b a o g 16) := by
  let I : Nat → State → Prop := fun left t => ∃ j, j<16 ∧ left=16-j ∧ LoopState s₀ b a o g j t
  refine WP.loop (M := isa) I (fun left t ⟨j,hj,hl,ht⟩ => ?_) (16-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (loop_step_ok hg hj ht hr hsep hbsep (hhin j hj) (hin j hj) (hw8 j hj) (hw4 j hj)) ?_
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


/-- At loop completion, the complete output buffer is the original encoding. -/
theorem LoopState.output_bytes {s₀ s : State} {b a o : Addr} {g : Nat}
    (hg : IsG g) (h : LoopState s₀ b a o g 16 s) :
    VG.Spec.Sha3.bytesAt s.mem o (32*packWidth g)=packed g s₀.mem b a := by
  apply List.ext_getElem
  · simp only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range,packed_length hg]
  · intro i hi hj
    simp only [VG.Spec.Sha3.bytesAt,List.getElem_map,List.getElem_range]
    rw [←getElem!_pos (packed g s₀.mem b a) i hj]
    apply h.values
    have hh : i<32*packWidth g := by
      simpa only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range] using hi
    have he : 2*packWidth g*16=32*packWidth g := by omega
    omega

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end
