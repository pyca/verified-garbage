import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

structure ParserState (s₀ : State) (a o : Addr) (d j : Nat) (s : State) : Prop where
  bound : j≤16
  ready : ParseReady d s
  values : Parsed s.mem o s₀.mem a d (16*j)
  frame : Frame [⟨o,1024⟩] s₀.mem s.mem
  input : s.gpr .x0=a+BitVec.ofNat 64 (2*d*j)
  output : s.gpr .x4=o+BitVec.ofNat 64 (64*j)
  count : s.gpr .x11=BitVec.ofNat 64 (16-j)
  gpr : ∀ r, r≠.x0 → r≠.x4 → r≠.x9 → r≠.x11 → s.gpr r=s₀.gpr r
  vec : ∀ v, v∉bodyTemps → s.v v=s₀.v v
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp

theorem parser_step_ok {s₀ s : State} {a o : Addr} {d j : Nat}
    (hd : d=18 ∨ d=20) (hj : j<16) (h : ParserState s₀ a o d j s)
    (hsep : (Region.mk a (32*d)).Disjoint ⟨o,1024⟩)
    (h0 : InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)) 16)
    (h1 : InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 (2*d-16)) 16)
    (hw : ∀ g<4, InRegions s₀.wr (o+BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block (Unpack.body d)) s (ParserState s₀ a o d (j+1)) := by
  refine WP.mono (body_ok s hd h.ready
    (by simpa only [h.rd,h.wr,h.input] using h0)
    (by simpa only [h.rd,h.wr,h.input] using h1)
    (by simpa only [h.rd,h.wr,h.input] using h2)
    (fun g hg => by simpa only [h.wr,h.output] using hw g hg)) ?_
  intro t ht
  have hf : Frame [⟨o+BitVec.ofNat 64 (64*j),64⟩] s.mem t.mem := by
    simpa only [h.output] using ht.frame
  have old : Parsed t.mem o s₀.mem a d (16*j) := h.values.keep (by omega) hf (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hs := Offset.disjoint o (d := 0) (n := 4*(16*j)) (e := 64*j) (k := 64)
      (Or.inl (by omega)) (by omega) (by omega)
    simpa only [BitVec.add_zero] using hs)
  refine ⟨by omega,ht.ready,?_,?_,?_,?_,?_,?_,?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩
  · intro i hi
    by_cases he : i<16*j
    · exact old i he
    · have hv := ht.words (i-16*j) (by omega)
      rw [h.output,h.input,Offset.add_add,fieldValue_shift _ _ hd] at hv
      rw [show 64*j+4*(i-16*j)=4*i by omega,show 16*j+(i-16*j)=i by omega] at hv
      rw [fieldValue_keep hd (by omega) h.frame (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hsep)] at hv
      exact hv
  · exact h.frame.trans (hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨⟨o,1024⟩,by simp,Offset.sub_base o (by omega)⟩))
  · rw [ht.input,h.input,Offset.add_add,Nat.mul_succ]
  · rw [ht.output,h.output]
    change (o+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=o+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.count,h.count]
    bv_omega
  · intro r h0 h4 h9 h11
    exact (ht.gpr r h0 h4 h9 h11).trans (h.gpr r h0 h4 h9 h11)
  · intro v hv
    exact (ht.vec v hv).trans (h.vec v hv)

/-- The sampler parser always executes exactly sixteen groups. -/
theorem parser_loop_ok {s₀ s : State} {a o : Addr} {d start : Nat}
    (hd : d=18 ∨ d=20) (hstart : start<16) (h : ParserState s₀ a o d start s)
    (hsep : (Region.mk a (32*d)).Disjoint ⟨o,1024⟩)
    (h0 : ∀ j<16, InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)) 16)
    (h1 : ∀ j<16, InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 16) 16)
    (h2 : ∀ j<16, InRegions (s₀.rd++s₀.wr) (a+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 (2*d-16)) 16)
    (hw : ∀ j<16, ∀ g<4, InRegions s₀.wr (o+BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.loop (.block (Unpack.body d)) (.nonzero .x .x11)) s (ParserState s₀ a o d 16) := by
  let I : Nat → State → Prop := fun left t => ∃ j, j<16 ∧ left=16-j ∧ ParserState s₀ a o d j t
  refine WP.loop (M := isa) I (fun left t ⟨j,hj,hl,ht⟩ => ?_) (16-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (parser_step_ok hd hj ht hsep (h0 j hj) (h1 j hj) (h2 j hj) (hw j hj)) ?_
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

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
